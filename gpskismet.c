/****************************************************************

Copyright (c) 2001-2004 Fritz Ganter <ganter@ganter.at>

Website: www.gpsdrive.de

Disclaimer: Please do not use for navigation.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    *********************************************************************


reads info from kismet server and insert waypoints into database

*****************************************************************/

// external
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <sys/time.h>
#include <glib/gstdio.h>
// my includes
#include <time.h>
#include <stdarg.h>
#include <glib.h>
#include <pthread.h>
// end my includes

// from GpsDrive
#include <gpsdrive.h>
#include "gpsdrive_config.h"
#include <poi.h>
#include <errno.h>
#include "database.h"
#include "gpskismet.h"

#ifdef SPEECH
#include "speech.h"
#endif

// Defines for gettext I18n
# include <libintl.h>
# define _(String) gettext(String)
# ifdef gettext_noop
#  define N_(String) gettext_noop(String)
# else
#  define N_(String) (String)
# endif

//////////////////////////////////////////////////////////////////////////////
// Variables
//////////////////////////////////////////////////////////////////////////////
// external variables
extern int mydebug, debug;

// internal variables - file scope limited
static char   kbuffer[20210];               // buffer sentences read from socket
static int    bc = 0;                       // count characters per sentence read from socket
static fd_set kismetreadmask;               // file descriptor set
static struct timeval kismettimeout;        // timeout for select() calls
static time_t last_initkismet=0;            // for initkismet()
static char   macaddr[30], lastmacaddr[30]; // for initkismet()

// data shared between the readkismet() thread and the main program
// (readkismet_threaded_)
static sig_atomic_t readkismet_complete = TRUE;

void readkismet_threaded_(gint * kismetsock){
  pthread_t thread_ID;
  pthread_attr_t thread_attr;
  int thread_state;
  if (readkismet_complete){
    if (debug) printf("GPS-Kismet: (THREAD) Previous readkismet thread finished, starting new thread\n");
    readkismet_complete = FALSE;
    pthread_attr_init(&thread_attr);
    pthread_attr_setdetachstate(&thread_attr,PTHREAD_CREATE_DETACHED);
    thread_state = pthread_create(&thread_ID,&thread_attr,readkismet_wrapper_,(void *)kismetsock);
    if (thread_state){
      printf("GPS-Kismet: (THREAD) Error: return code from pthread_create() is: \"%d\"\n",thread_state);
      // the thread failed to start, so set its status to completed
      readkismet_complete = TRUE;
    }
    // now that the thread has been created, the attributes can be freed
    pthread_attr_destroy(&thread_attr);
  }
  else {
    if (debug) printf("GPS-Kismet: (THREAD) Previous readkismet thread still running, not starting a new thread\n");
  }
}

void * readkismet_wrapper_(void * generic_pointer){
  if (debug) printf("GPS-Kismet: (THREAD) Starting readkismet thread\n");
  if (debug) printf("GPS-Kismet: (THREAD) Pushing readkismet_cleanup_ on the stack of cleanup handlers\n");
  pthread_cleanup_push(readkismet_cleanup_,NULL);
  readkismet((gint *)generic_pointer);
  sched_yield();
  if (debug) printf("GPS-Kismet: (THREAD) Ending readkismet thread\n");
  pthread_cleanup_pop(1);
  return NULL;
}

void readkismet_cleanup_(void * generic_pointer){
  if (debug) printf("GPS-Kismet: (THREAD) Setting readkismet_complete = TRUE\n");
  readkismet_complete = TRUE;
}

void readkismet (gint * kismetsock) {
    // TODO: 
    // source_id for kismet is currently hardcoded to 9
    //  maybe we should ask geoinfo.db the value at startup
    // general cleanup, removing unecessary variables and scopes
    //  fix static vs global scoping
    // better variable names, consistent functions (glib or not..)
    // use strncpy instead of strcpy when modifying kisNet
    //  (or a glib function)
    // double-check the Kismet protocol definitions
    //  I don't think my interpretation of some of the values
    //  is correct
    // look up the (bssid AND ssid) when deciding whether or not
    //  to update or insert new values into the database    
    //  (requires modifying database.c)
    // If SSID is an empty string, insert a default replacement
    //  into the database (perhaps <ANY> :: from kismet_client)
    // Database: figure what is escaping the sql_escape function
    //  and causing an SQL syntax error
    // Figure out why some networks in poi_extra have poi_id = -1
    // Reworking the database functions
    // Add altitude information
    // general speedup. Only think I can think of atm is threading
    //  or a fork
    // ...
    // Immediate TODO
    // ...

  signed char c;                            // c          - buffer a single character read from the socket
  int e;                                    // e          - count number of segments read: (char) from socket, (char *) from parseKisProto
  int haveInput;                            // haveInput  - boolean describing return value of FD_ISSET()
  int selection;                            // selection  - boolean describing return value of select()
                                            
  // my variables
  const time_t NET_SYNCH_INTERVAL = 10;     // seconds between database updates
  const time_t NET_SCRUB_INTERVAL = 120;    // seconds between hash table scrubbing
  const time_t MAX_NET_LIFE = 600;          // maximum age of network, in seconds
  const time_t MAX_UPDATE_SILENCE = 300;    // how many seconds before a network without updates is deleted
  static time_t last_synch_time = 0;
  static time_t last_scrub_time = 0;
  char * kisArray [6];                      // hold temporary data from parseKisProto()
  static GHashTable * gKisHash = NULL;
  // end my variables

  //////////////////////////////////////////////////////////////////////////////
  // On First Run Only
  //////////////////////////////////////////////////////////////////////////////
  // initialize default values:
  // default values have static function scoping, and so are
  // persistent across function calls
  // 0 is an improbable time but a valid boolean
  if (!last_synch_time)   last_synch_time = time(NULL);
  if (!last_scrub_time)   last_scrub_time = time(NULL);
  if (gKisHash == NULL)   gKisHash        = g_hash_table_new_full(g_str_hash,g_str_equal,NULL,free);

  //////////////////////////////////////////////////////////////////////////////
  // Run even without a kismet connection
  //////////////////////////////////////////////////////////////////////////////
  // Only bother if there's been a kismet connection before
  // Synch any data that didnt make it before the connection was lost
  if (last_synch_time + NET_SYNCH_INTERVAL <= time(NULL)) {
    //kisHashSynch(gKisHash);
    kisHashSynch_threaded_(gKisHash);
    last_synch_time = time(NULL);
  }
  // even if the kismet connection has been lost we want to free memory
  if (last_scrub_time + NET_SCRUB_INTERVAL <= time(NULL)){
    kisHashScrub(gKisHash,MAX_UPDATE_SILENCE,MAX_NET_LIFE);
    last_scrub_time = time(NULL);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Kismet Connection Code
  //////////////////////////////////////////////////////////////////////////////
  // If Kismet server connection failed, Try to reconnect
  //  after at least 30 seconds
  if ((*kismetsock<0) && ((time(NULL) - last_initkismet) > 30)) {
    if (debug) g_print(_("trying to re-connect to kismet server\n"));
    *kismetsock = initkismet();
    if (*kismetsock>=0) g_print(_("Kismet server connection re-established\n"));
    if (debug) g_print(_("done trying to re-connect: socket=%d\n"),*kismetsock);
  }
  // if 30 seconds have yet to pass, or the kismet
  //  connection just failed, return
  if (*kismetsock < 0) return;


  //////////////////////////////////////////////////////////////////////////////
  // While Connection Established
  //////////////////////////////////////////////////////////////////////////////
  // loop while there is data to read:
  // depending on how much information (and how backed up the socket is)
  // there could be one or multiple lines of data - no guarantees
  do {
    e = 0;
    FD_ZERO (&kismetreadmask);
    FD_SET (*kismetsock, &kismetreadmask);
    kismettimeout.tv_sec = 0;
    kismettimeout.tv_usec = 10000;

    // select() blocks until there is activity on the file descriptor, or until
    // the timeout period has expired. Return values:
    //  -1  error
    //   0  timeout
    //   _  number of ready file descriptors
    // if there was an error: close the socket, set kismetsock to -1 (error) and return
    if ((selection = select(FD_SETSIZE,&kismetreadmask,NULL,NULL,&kismettimeout)) < 0) {
      perror ("readkismet: select() call");
      close(*kismetsock);
      *kismetsock = -1;
      return;
    }
    // if the timeout expired or no file descriptors are ready (selection == 0), 
    // continue the loop: synching, scrubbing...

    // set the condition for the data-processing loop to continue
    // read the data into kbuffer, if available
    // return from the function in case of failure
    if ((haveInput = FD_ISSET (*kismetsock, &kismetreadmask))) {
      int bytesread;
      bytesread=0;
      while ((e = read (*kismetsock, &c, 1)) > 0) {
        bytesread++;
        if (c != '\n') {
          *(kbuffer + bc++) = c;
        }
        else {
          c = -1;
          g_strlcat (kbuffer, "\n", sizeof (kbuffer));
          /*  g_print("\nfinished: %d",bc); */
          break;
        }
        if (bc > 20000) {
          bc = 0;
          g_print ("kbuffer overflow!\n");
        }
      }
      // the file descriptor was ready for read but no data available...
      // this means the connection was lost. Close the socket, set
      // kismetsock to -1 (error) and return.
      if (bytesread==0) {
        g_print(_("Kismet server connection lost\n"));
        close(*kismetsock);
        *kismetsock = -1;
        return;
      }
    }

    // a line of data has been read, begin processing
    if (c == -1) {
      // reset some values
      bc = c = 0;
      if (strstr(kbuffer,"*BSSID:") == kbuffer){
        if (debug) printf("GPS-Kismet: Kismet BSSID Sentence: \"%s\"\n",kbuffer);
        // get: bssid, channel, minlat, minlon, bestlat, bestlon
        e = parseKisProto(kbuffer,kisArray,6,0,1,2,3,4,5);
        if (debug) printf("GPS-Kismet: Sentence fields parsed: \"%d\"\n",e);
        if (e == 6){
          insertBSSID(gKisHash,kisArray[0],kisArray[1],kisArray[2],kisArray[3],kisArray[4],kisArray[5]);
        }
        for (int i=0; i<e; i++){
          free(kisArray[i]);
        }
      }
      if (strstr (kbuffer,"*SSID:") == kbuffer) {
        if (debug) printf ("GPS-Kismet: Kismet SSID Sentence: \"%s\"\n",kbuffer);
        // get: mac, type, ssid, cryptset, cloaked
        e = parseKisProto(kbuffer,kisArray,5,0,1,2,3,4);
        if (debug) printf("GPS-KISMET: Sentence fields parsed: \"%d\"\n",e);
        if (e == 5) {
          insertSSID(gKisHash,kisArray[0],kisArray[1],kisArray[2],kisArray[3],kisArray[4]);
        }
        for (int i=0; i<e; i++){
          free(kisArray[i]);
        }
      }
      memset (kbuffer, 0, 20000);
      g_strlcpy (kbuffer, "", sizeof (kbuffer));
    }

    // Display some timing information for debugging
    if (debug) printTimings(last_synch_time,NET_SYNCH_INTERVAL,last_scrub_time,NET_SCRUB_INTERVAL);

    // synchronize with the SQLite database if:
    //  . at least NET_SYNCH_INTERVAL time has passed since the last sync
    //  . lost the kismet connection, might as well upload all the data we have
    //    (at least 30 wait before a reconnect is attempted)
    if (last_synch_time + NET_SYNCH_INTERVAL <= time(NULL)) {
      //kisHashSynch(gKisHash);
      kisHashSynch_threaded_(gKisHash);
      last_synch_time = time(NULL);
    }
    // scrub the hash table:
    //  entries which haven't been updated for MAX_UPDATED_SILENCE are removed
    //  entries which are older than MAX_NET_LIFE are removed
    if (last_scrub_time + NET_SCRUB_INTERVAL <= time(NULL)){
      kisHashScrub(gKisHash,MAX_UPDATE_SILENCE,MAX_NET_LIFE);
      last_scrub_time = time(NULL);
    }

  }
  while (haveInput != 0);
}

int initkismet (void) {
  struct sockaddr_in server;
  struct hostent *server_data;
  char buf[180];
  gint t_sock;
  last_initkismet=time(NULL);

  if (debug) g_print(_("Trying Kismet server\n"));

  g_strlcpy (lastmacaddr, "", sizeof (lastmacaddr));
  /*  open socket to port */
  if ((t_sock = socket (AF_INET, SOCK_STREAM, 0)) < 0) {
    perror (_("can't open socket for port "));
    return -1;
  }
  server.sin_family = AF_INET;
  /*  We retrieve the IP address of the server from its name: */
  if ((server_data = gethostbyname(local_config.kismet_servername)) == NULL) {
    fprintf (stderr, "%s: unknown host", local_config.kismet_servername);
    close (t_sock);
    return -1;
  }
  memcpy (&server.sin_addr, server_data->h_addr, server_data->h_length);
  server.sin_port = htons (local_config.kismet_serverport);
  /*  We initiate the connection  */
  if (connect (t_sock, (struct sockaddr *) &server, sizeof server) < 0) {
    close (t_sock);
    return -1;
  }
  else {
    g_strlcpy (buf,
      "!0 ENABLE BSSID bssid,channel,minlat,minlon,bestlat,bestlon\n",
      sizeof (buf));
    write (t_sock, buf, strlen (buf));
    g_strlcpy (buf,
      "!0 ENABLE SSID mac,type,ssid,cryptset,cloaked\n",
      sizeof (buf));
    write (t_sock, buf, strlen (buf));
  }

  return t_sock;
}

int parseKisProto(const char * kisStr, char ** kisArray, const int fieldsKeep, ...){
  int increment = 0;
  int fieldsSeen = 0;
  int fieldsKept = 0;
  int keepIndex;
  const char * currKisLoc = kisStr;
  const char * nextKisLoc = NULL;
  const char * lastKisLoc = kisStr + strlen(kisStr);
  //char printBuffer [256];
  va_list vaListPtr;
  va_start(vaListPtr,fieldsKeep);
  if (fieldsKeep > 0){
    keepIndex = va_arg(vaListPtr,int);
  }
  // strip off the footer, if it's a newline
  // and if the string is long enough
  if (lastKisLoc - kisStr > 0 && *(lastKisLoc - 1) == '\n'){
    lastKisLoc--;
  }
  // strip off the header
  currKisLoc = strpbrk(kisStr," ");
  if (currKisLoc == NULL)
    currKisLoc = lastKisLoc;
  else
    currKisLoc++;
  // parse the data fields
  while(lastKisLoc - currKisLoc > 0 && (fieldsKeep < 0 || fieldsKept < fieldsKeep)){
    if (*currKisLoc == '\001'){
      currKisLoc++;
      nextKisLoc = strpbrk(currKisLoc,"\001");
      if (nextKisLoc == NULL){
        nextKisLoc = lastKisLoc;
        increment = 0;
      }
      else if (lastKisLoc - nextKisLoc > 1 && *(nextKisLoc + 1) == ' '){
        increment = 2;
      }
      else{
        increment = 1;
      }
    }
    else {
      nextKisLoc = strpbrk(currKisLoc," ");
      if (nextKisLoc == NULL){
        nextKisLoc = lastKisLoc;
        increment = 0;
      }
      else{
        increment = 1;
      }
    }
    // process the data
    if (fieldsKeep < 0 || (fieldsKept < fieldsKeep && keepIndex == fieldsSeen)){
      kisArray[fieldsKept] = (char *)malloc(sizeof(char) * (nextKisLoc - currKisLoc + 1));
      strncpy(kisArray[fieldsKept],currKisLoc,nextKisLoc - currKisLoc);
      kisArray[fieldsKept][nextKisLoc - currKisLoc] = '\0';
      //cout << "Field:\t\"" << kisArray[fieldsKept] << "\"" << endl;
      //printf("Field:\t\"%s\"\n",kisArray[fieldsKept]);
      fieldsKept++;
      if (fieldsKeep > 0){
        keepIndex = va_arg(vaListPtr,int);
      }
    }
    // setup for the next data field
    currKisLoc = nextKisLoc + increment;
    increment = 0;
    fieldsSeen++;
  }
  va_end(vaListPtr);
  return fieldsKept;
}

void printKisNet(const char * prefix,const gboolean full,const network * kisNet) {
  printf("%sNetwork struct information:\n",prefix);
  if (kisNet->bssid_sentence || kisNet->ssid_sentence){
    printf("%s Common sentence data\n",prefix);
    printf("%s  bssid:      %s\n",prefix,kisNet->bssid);
  }
  if (kisNet->bssid_sentence){
    printf("%s BSSID-specific sentence data\n",prefix);
    printf("%s  channel:    %d\n",prefix,kisNet->channel);
    printf("%s  minlat:     %f\n",prefix,kisNet->minlat);
    printf("%s  minlon:     %f\n",prefix,kisNet->minlon);
    printf("%s  bestlat:    %f\n",prefix,kisNet->bestlat);
    printf("%s  bestlon:    %f\n",prefix,kisNet->bestlon);
  }
  if (kisNet->ssid_sentence){
    printf("%s SSID-specific sentence data\n",prefix);
    printf("%s  ssid:       %s\n",prefix,kisNet->ssid);
    printf("%s  type:       %d\n",prefix,kisNet->type);
    printf("%s  cryptset:   %d\n",prefix,kisNet->cryptset);
    printf("%s  cloaked:    %d\n",prefix,kisNet->cloaked);
    printf("%s SSID-derived data\n",prefix);
    printf("%s  type_desc:  %s\n",prefix,kisNet->type_desc);
    printf("%s  poi_Type:   %s\n",prefix,kisNet->poi_type);
  }
  if (full){
    printf("%s Administrative data\n",prefix);
    printf("%s  bssid_sentence:       %d\n",prefix,kisNet->bssid_sentence);
    printf("%s  ssid_sentence:        %d\n",prefix,kisNet->ssid_sentence);
    printf("%s  time_created:         %d\n",prefix,(int)kisNet->time_created);
    printf("%s  time_updated:         %d\n",prefix,(int)kisNet->time_updated);
    printf("%s  modified_since_sync:  %d\n",prefix,kisNet->modified_since_sync);
  }
  printf("%sEND Network struct information:\n",prefix);
  return;
}

void kisNetSynch(network * kisNet){
  glong sqlid     = 0;
  gchar speech_buffer     [100];  // 50 (max length of network->ssid) + 50 (max custom text) + 50 (spare memory)
  gchar conversion_buffer [5];    // used for converting strings to numbers - doesn't need to be large

  sqlid = db_poi_extra_get(NULL,"bssid",kisNet->bssid,NULL);
  // this is an existing network, but update the values
  if (sqlid > 0){
    if (debug) printf("GPS-Kismet: Found matching entry in database for network with bssid:\"%s\"\n",kisNet->bssid);
    // GPS values are no good, these are the default values from kismet if no GPS is present
    if (kisNet->bestlat != 0.0 && kisNet->bestlon != 0.0){
      db_poi_edit(sqlid,kisNet->bestlat,kisNet->bestlon,kisNet->ssid,kisNet->poi_type,kisNet->bssid,9,TRUE);
      // sentence data that should not have changed
      //g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->type);
      //db_poi_extra_edit(&sqlid,"type",conversion_buffer,TRUE);
      //db_poi_extra_edit(&sqlid,"type_desc",kisNet->type_desc,TRUE);
      //g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->cryptset);
      //db_poi_extra_edit(&sqlid,"cryptset",conversion_buffer,TRUE);
      //g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->cloaked);
      //db_poi_extra_edit(&sqlid,"cloaked",conversion_buffer,TRUE);
      //g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->channel);
      //db_poi_extra_edit(&sqlid,"channel",conversion_buffer,TRUE);
      // no need to update bssid, we already know it matches
      if (debug) printf("GPS-Kismet: Updating database with network struct identified by bssid:\"%s\"\n",kisNet->bssid);
    }
    else if (debug){
      printf("GPS-Kismet: Could not update database with network struct identified by bssid:\"%s\", invalid GPS data\n",kisNet->bssid);
    }
  }
  // this is a new network, we store it in the database
  else{
    if (debug) printf("GPS-Kismet: Could not find matching entry in database for network with bssid:\"%s\"\n",kisNet->bssid);
    // GPS values are no good, these are the default values from kismet if no GPS is present
    if (kisNet->minlat != 90.0 && kisNet->minlon != 180.0){
      sqlid = db_poi_edit(0,kisNet->minlat,kisNet->minlon,kisNet->ssid,kisNet->poi_type,kisNet->bssid,9,FALSE);
      g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->type);
      db_poi_extra_edit(&sqlid,"type",conversion_buffer,FALSE);
      db_poi_extra_edit(&sqlid,"type_desc",kisNet->type_desc,FALSE);
      g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->cryptset);
      db_poi_extra_edit(&sqlid,"cryptset",conversion_buffer,FALSE);
      g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->cloaked);
      db_poi_extra_edit(&sqlid,"cloaked",conversion_buffer,FALSE);
      g_snprintf(conversion_buffer,sizeof(conversion_buffer),"%d",kisNet->channel);
      db_poi_extra_edit(&sqlid,"channel",conversion_buffer,FALSE);
      // one duplicated value (bssid) to allow db_poi_extra_get to work
      // should be removed once db_poi_get from database.c is working
      db_poi_extra_edit(&sqlid,"bssid",kisNet->bssid,FALSE);

      g_snprintf (speech_buffer,sizeof(speech_buffer),_("Found new %s access point: %s"),_(kisNet->poi_type),_(kisNet->ssid));
      #ifdef SPEECH
      speech_saytext (speech_buffer, 3);
      #endif
      if (debug) printf("GPS-Kismet: Inserting into database network struct identified by bssid:\"%s\"\n",kisNet->bssid);
    }
    else if (debug){
      printf("GPS-Kismet: Could not insert into database network struct identified by bssid:\"%s\", invalid GPS data\n",kisNet->bssid);
    }
  }
}

void kisHashSynch(GHashTable * gKisHash){
  GHashTableIter gKisHashIter;
  gpointer gKisHashKey;
  gpointer gKisHashVal;
  network * kisNet = NULL;

  if (debug) printf("GPS-Kismet: Starting database update cycle\n");
  g_hash_table_iter_init(&gKisHashIter,gKisHash);
  while(g_hash_table_iter_next(&gKisHashIter,&gKisHashKey,&gKisHashVal)){
    kisNet = gKisHashVal;
    // is all the network data available ?
    // has it been modified since the last sync ?
    if (kisNet->ssid_sentence && kisNet->bssid_sentence && kisNet->modified_since_sync){
      if (debug) printf("GPS-Kismet: Network with bssid:\"%s\" will by synched with database\n",kisNet->bssid);
      kisNetSynch(kisNet);
      kisNet->modified_since_sync = FALSE;
    }
  }
  if (debug) printf("GPS-Kismet: End database update cycle\n");
}

// this function's call stack should not modify any of the GpsDrive global variables
// none of the GpsDrive functions called have static variables
// none of the external libraries were vetted for re-entrant behavior
void kisHashSynch_threaded_(GHashTable * gKisHash){
  static pthread_t thread_ID;
  static gboolean thread_exists = FALSE;
  pthread_attr_t thread_attr;
  int thread_state;
  // glibc hash tables are not thread-safe
  // we can't have the threaded database synch functions reading
  // from a currently mutable hash table, while:
  //  entries insert by: insertSSID() and insertBSSID()
  //  entries removed by: kisHashScrub()
  // Solution: create a filtered 'snapshot' of gKisHash containing
  // only copies of networks which can be synched
  // This copy and its contents should be destroyed within the thread
  // when it is no longer needed
  GHashTable * gKisHashCopy;
  GHashTableIter gKisHashIter;
  gpointer gKisHashKey;
  gpointer gKisHashVal;
  network * kisNet        = NULL;
  network * copiedKisNet  = NULL;

  // a mutex would just lock out the main program
  // snapshot approach allows concurrent execution
  if (debug) printf("GPS-Kismet: (THREAD) Creating a second hash table copying only networks ready to by synched\n");
  gKisHashCopy = g_hash_table_new_full(g_str_hash,g_str_equal,NULL,free);
  g_hash_table_iter_init(&gKisHashIter,gKisHash);
  while(g_hash_table_iter_next(&gKisHashIter,&gKisHashKey,&gKisHashVal)){
    kisNet = gKisHashVal;
    if (kisNet->ssid_sentence && kisNet->bssid_sentence && kisNet->modified_since_sync){
      copiedKisNet = kisNetCopy(kisNet);
      g_hash_table_insert(gKisHashCopy,copiedKisNet->bssid,copiedKisNet);
    }
  }
  
  if (thread_exists){
    if (debug) printf("GPS-Kismet: (THREAD) Joining the previous kisHashSynch thread\n");
    time_t before_waiting = time(NULL);
    thread_state  = pthread_join(thread_ID,NULL);
    thread_exists = FALSE;
    time_t after_waiting  = time(NULL);
    if (debug) printf("GPS-Kismet: (THREAD) Waited %d seconds for previous kisHashSynch thread to finish\n",(int)(after_waiting - before_waiting));
  }
  if (thread_state) {
    printf("GPS-Kismet: (THREAD) Error: return code from pthread_join() is: \"%d\"\n",thread_state);
  }
  pthread_attr_init(&thread_attr);
  pthread_attr_setdetachstate(&thread_attr,PTHREAD_CREATE_JOINABLE);
  thread_state = pthread_create(&thread_ID,&thread_attr,kisHashSynch_wrapper_,(void *)gKisHashCopy);
  if (thread_state){
    printf("GPS-Kismet: (THREAD) Error: return code from pthread_create() is: \"%d\"\n",thread_state);
  }
  else{
    thread_exists = TRUE;
  }
  // now that the thread has been created, the attributes can be freed
  pthread_attr_destroy(&thread_attr);
}

void * kisHashSynch_wrapper_(void * generic_pointer){
  if (debug) printf("GPS-Kismet: (THREAD) Starting kisHashSynch thread\n");
  kisHashSynch((GHashTable *)generic_pointer);
  if (debug) printf("GPS-Kismet: (THREAD) Finished database synch, freeing the copied hash table and contained networks\n");
  g_hash_table_destroy((GHashTable *)generic_pointer);
  sched_yield();
  if (debug) printf("GPS-Kismet: (THREAD) Ending kisHashSynch thread\n");
  return NULL;
}

void kisHashScrub(GHashTable * gKisHash, const time_t MAX_UPDATE_SILENCE, const time_t MAX_NET_LIFE){
  GHashTableIter gKisHashIter;
  gpointer gKisHashKey;
  gpointer gKisHashVal;
  network * kisNet = NULL;

  if (debug) printf("GPS-Kismet: Starting hash table scrub cycle\n");
  g_hash_table_iter_init(&gKisHashIter,gKisHash);
  while(g_hash_table_iter_next(&gKisHashIter,&gKisHashKey,&gKisHashVal)){
    kisNet = gKisHashVal;
    // how long since the last update ?
    if (kisNet->time_updated + MAX_UPDATE_SILENCE <= time(NULL)){
      if (debug) printf("GPS-Kismet: network identified by bssid:\"%s\" has not been updated in at least %d seconds, removing\n",kisNet->bssid,(int)MAX_UPDATE_SILENCE);
      g_hash_table_iter_remove(&gKisHashIter);
    }
    // how long has the entry been alive ?
    else if (kisNet->time_created + MAX_NET_LIFE <= time(NULL)){
      if (debug) printf("GPS-Kismet: network identified by bssid:\"%s\" has reached maximum age of %d seconds, removing\n",kisNet->bssid,(int)MAX_NET_LIFE);
      g_hash_table_iter_remove(&gKisHashIter);
    }
  }
  if (debug) printf("GPS-Kismet: End hash table scrub cycle\n");
}

void insertBSSID(GHashTable * gKisHash, const char * bssid, const char * channel, const char * minlat, const char * minlon, const char * bestlat, const char * bestlon){
  gpointer gKisHashKey;
  gpointer gKisHashVal;
  network * kisNet = NULL;

  // bssid already present in hash table, only update the necessary fields
  if (g_hash_table_lookup_extended(gKisHash,bssid,&gKisHashKey,&gKisHashVal)){
    if (debug) printf("GPS-Kismet: Updating BSSID fields of network struct\n");
    kisNet = gKisHashVal;
    kisNet->minlat   = g_strtod(minlat,   NULL);
    kisNet->minlon   = g_strtod(minlon,   NULL);
    kisNet->bestlat  = g_strtod(bestlat,  NULL);
    kisNet->bestlon  = g_strtod(bestlon,  NULL);
    // kisNet doesn't hold BSSID sentence data yet
    if (!kisNet->bssid_sentence){
      kisNet->channel  = atoi(channel);
      // set administrative values
      kisNet->bssid_sentence = TRUE;
    }
    // set administrative values
    kisNet->time_updated = time(NULL);
    kisNet->modified_since_sync = TRUE;
  }
  // otherwise create a new network struct entry and insert it into the hash table
  else {
    if (debug) printf("GPS-Kismet: Creating new network struct with BSSID data\n");
    kisNet = (network *)malloc(sizeof(network));
    strcpy(kisNet->bssid,bssid);
    kisNet->channel  = atoi(channel);
    kisNet->minlat   = g_strtod(minlat,   NULL);
    kisNet->minlon   = g_strtod(minlon,   NULL);
    kisNet->bestlat  = g_strtod(bestlat,  NULL);
    kisNet->bestlon  = g_strtod(bestlon,  NULL);
    // set administrative values
    kisNet->bssid_sentence = TRUE;
    kisNet->ssid_sentence = FALSE;
    kisNet->time_created = time(NULL);
    kisNet->time_updated = kisNet->time_created;
    kisNet->modified_since_sync = TRUE;
    // now, inserting the key into the hash table:
    //  if the key already exists (which shouldn't happend), 
    //  g_hash_table_insert() calls value_destroy_func and
    //  key_destroy_func (if defined) before replacing the
    //  value
    g_hash_table_insert(gKisHash,kisNet->bssid,kisNet);
  }
  if (debug) printKisNet("GPS-Kismet: ",TRUE,kisNet);
}

void insertSSID(GHashTable * gKisHash, const char * mac, const char * type, const char * ssid, const char * cryptset, const char * cloaked){
  gpointer gKisHashKey;
  gpointer gKisHashVal;
  network * kisNet = NULL;
  const gchar * type_string []  = {"infrastructure","ad-hoc","probe","data","turbocell","unknown"};
  const gchar * poi_type []     = {"wlan.open","wlan.wep","wlan.closed"};

  // mac/bssid already present in the hash table, only update the necessary fields
  if (g_hash_table_lookup_extended(gKisHash,mac,&gKisHashKey,&gKisHashVal)){
    if (debug) printf("GPS-Kismet: Updating SSID fields of network struct\n");
    kisNet = gKisHashVal;
    // kisNet doesn't hold SSID sentence data yet
    if (!kisNet->ssid_sentence){
      strcpy(kisNet->ssid,ssid);
      kisNet->type      = atoi(type);
      kisNet->cryptset  = atoi(cryptset);
      kisNet->cloaked   = atoi(cloaked);
      // set derived values for GpsDrive
      if (kisNet->cryptset > 2){
        strcpy(kisNet->poi_type,poi_type[2]);
      }
      else{
        strcpy(kisNet->poi_type,poi_type[kisNet->cryptset]);
      }
      if (kisNet->type > 5){
        strcpy(kisNet->type_desc,type_string[5]);
      }
      else{
        strcpy(kisNet->type_desc,type_string[kisNet->type]);
      }
      // set administrative values
      kisNet->ssid_sentence = TRUE;
      kisNet->modified_since_sync = TRUE;
    }
    // set administrative values
    kisNet->time_updated = time(NULL);
  }
  // otherwise create a new network struct entry and insert it into the hash table
  else {
    if (debug) printf("GPS-Kismet: Creating new network struct with SSID data\n");
    kisNet = (network *)malloc(sizeof(network));
    strcpy(kisNet->bssid, mac);
    strcpy(kisNet->ssid,  ssid);
    kisNet->type      = atoi(type);
    kisNet->cryptset  = atoi(cryptset);
    kisNet->cloaked   = atoi(cloaked);
    // set derived values for GpsDrive
    if (kisNet->cryptset > 2){
      strcpy(kisNet->poi_type,poi_type[2]);
    }
    else{
      strcpy(kisNet->poi_type,poi_type[kisNet->cryptset]);
    }
    if (kisNet->type > 5){
      strcpy(kisNet->type_desc,type_string[5]);
    }
    else{
      strcpy(kisNet->type_desc,type_string[kisNet->type]);
    }
    // set administrative values
    kisNet->ssid_sentence = TRUE;
    kisNet->bssid_sentence = FALSE;
    kisNet->time_created = time(NULL);
    kisNet->time_updated = kisNet->time_created;
    kisNet->modified_since_sync = TRUE;
    // now, inserting the key into the hash table
    g_hash_table_insert(gKisHash,kisNet->bssid,kisNet);
  }
  if (debug) printKisNet("GPS-Kismet: ",TRUE,kisNet);
}

void printTimings(const time_t last_synch_time, const time_t NET_SYNCH_INTERVAL, const time_t last_scrub_time, const time_t NET_SCRUB_INTERVAL){
  printf("GPS-Kismet: START Time information:\n");
  printf("GPS-Kismet:  Current Time: \"%d\"\n",(int)time(NULL));
  printf("GPS-Kismet:  Last Synch Time: \"%d\"\n",(int)last_synch_time);
  printf("GPS-Kismet:  Network Synch Interval: \"%d\"\n",(int)NET_SYNCH_INTERVAL);
  printf("GPS-Kismet:  Time-to-Synch: \"%d\"\n",(int)(NET_SYNCH_INTERVAL - (time(NULL)-last_synch_time)));
  printf("GPS-Kismet:  Last Scrub Time: \"%d\"\n",(int)last_scrub_time);
  printf("GPS-Kismet:  Network Scrub Interval: \"%d\"\n",(int)NET_SCRUB_INTERVAL);
  printf("GPS-Kismet:  Time-to-Scrub: \"%d\"\n",(int)(NET_SCRUB_INTERVAL - (time(NULL)-last_scrub_time)));
  printf("GPS-Kismet: END Time information:\n");
}

network * kisNetCopy(const network * kisNet) {
  network * copiedKisNet = (network *)malloc(sizeof(network));

  if (kisNet->bssid_sentence || kisNet->ssid_sentence){
    // copy common sentence data which we know to be present
    strcpy(copiedKisNet->bssid,kisNet->bssid);          // network struct: (gchar bssid [50])
  }
  if (kisNet->bssid_sentence){
    // copy BSSID-specific sentence data which we know to be present
    copiedKisNet->channel = kisNet->channel;
    copiedKisNet->minlat  = kisNet->minlat;
    copiedKisNet->minlon  = kisNet->minlon;
    copiedKisNet->bestlat = kisNet->bestlat;
    copiedKisNet->bestlon = kisNet->bestlon;
  }
  if (kisNet->ssid_sentence){
    // copy SSID-specific sentence data which we know to be present
    strcpy(copiedKisNet->ssid,kisNet->ssid);            // network struct: (gchar ssid [50])
    copiedKisNet->type      = kisNet->type;
    copiedKisNet->cryptset  = kisNet->cryptset;
    copiedKisNet->cloaked   = kisNet->cloaked;
    // now copy SSID-derived data
    strcpy(copiedKisNet->type_desc,kisNet->type_desc);  // network struct (gchar type_desc [50])
    strcpy(copiedKisNet->poi_type,kisNet->poi_type);    // network struct (gchar poi_type [50])
  }
  // copy administrative data which should always be present
  copiedKisNet->bssid_sentence        = kisNet->bssid_sentence;
  copiedKisNet->ssid_sentence         = kisNet->ssid_sentence;
  copiedKisNet->time_created          = kisNet->time_created;
  copiedKisNet->time_updated          = kisNet->time_updated;
  copiedKisNet->modified_since_sync   = kisNet->modified_since_sync;
  return copiedKisNet;
}

// vim:set ts=2 sw=2 et: