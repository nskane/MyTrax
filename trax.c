#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <unistd.h>


#define BMAX 512
#define BMAX_2 (512/2)
#define MAX_DEPTH 32

#define BLANK 0x00
#define RED   1
#define WHITE 2
#define RIGHT 0x01
#define UPPER 0x02
#define LEFT  0x04
#define LOWER 0x08
#define VERTICAL_W (UPPER | LOWER)    // "+" 1010 0x0a
#define HORIZONTAL_W (RIGHT | LEFT)   // "+" 0101 0x05
#define UPPER_LEFT_W (UPPER | LEFT)   // "/" 0110 0x06
#define LOWER_RIGHT_W (RIGHT | LOWER) // "/" 1001 0x09
#define UPPER_RIGHT_W (RIGHT | UPPER) // "\" 0011 0x03
#define LOWER_LEFT_W (LEFT | LOWER)   // "\" 1100 0x0c
#define VW  VERTICAL_W    //定跡入力用
#define HW  HORIZONTAL_W  //定跡入力用
#define ULW UPPER_LEFT_W  //定跡入力用
#define LRW LOWER_RIGHT_W //定跡入力用
#define URW UPPER_RIGHT_W //定跡入力用
#define LLW LOWER_LEFT_W  //定跡入力用

#define loop_number 20

int TLIST[6] = {VW, HW, ULW, LRW, URW, LLW};

int loop_start[loop_number][2][2];
int loop_start_next[loop_number][2][2];
int start[loop_number][2];
int loop_end[loop_number][2][2];
int loop_end_next[loop_number][2][2];
int end[loop_number][2];
int force_flag = 0;
int loop_force[10][2];
int loop_win = -1;
int riichi=-1;
int lost_check=-1; //1手で自分も相手もリーチがかかる場合

int board[BMAX][BMAX];
char ForceTile[LLW+1][LLW+1][LLW+1][LLW+1];
unsigned short PlaceableTile[LLW+1][LLW+1][LLW+1][LLW+1]; // 28561×2バイト＝56KB
unsigned long long random_t[BMAX][BMAX][LLW+1];
unsigned long long hash;

#define HASHWIDTH 0xffffff
unsigned long long HASH_TBL[HASHWIDTH+1]; // 2^24×64バイト＝512MB
char WINLOSS[HASHWIDTH+1]; // 16MB
unsigned int hash_cnt;

int x_min, x_max, y_min, y_max;
double t1, t2;
int max_depth;

static int killer_x[MAX_DEPTH+1], killer_y[MAX_DEPTH+1], killer_t[MAX_DEPTH+1];

char *color_s[3] = {"", "RED", "WHITE"};
char mark[LLW+1] = {'\0','\0','\0','\\','\0','+','/','\0','\0','/','+','\0','\\'};
char *b_string[LLW+1] = {" ", "", "", "\\","","+","\x1b[31m/\x1b[0m","","","/","\x1b[31m+\x1b[0m","","\x1b[31m\\\x1b[0m"};


double my_clock()
{
  struct timeval tv;
  gettimeofday(&tv, NULL);
  return tv.tv_sec + (double)tv.tv_usec*1e-6;
}

void initForceTile(){
  int i, j, k, l, m;
  int t[7] = {0x00, 0x03, 0x05, 0x06, 0x09, 0x0a, 0x0c};

  for(i = 0; i < 7; i++){
    for(j = 0; j < 7; j++){
      for(k = 0; k < 7; k++){
        for(l = 0; l < 7; l++){
          int wt = (((t[l] & UPPER)!=0) << 3 ) | (((t[k] & RIGHT)!=0) << 2) | (((t[j] & LOWER)!=0) << 1 ) | ((t[i] & LEFT)!=0);
          int rt;
          rt = (t[l] == 0 ? 0 : ((~t[l] & UPPER) != 0) << 3);
          rt |= (t[k] == 0 ? 0 : ((~t[k] & RIGHT) != 0) << 2);
          rt |= (t[j] == 0 ? 0 : ((~t[j] & LOWER) != 0) << 1);
          rt |= (t[i] == 0 ? 0 : (~t[i] & LEFT) != 0);
          rt &= 0x0f;
	  if( __builtin_popcount(wt) >= 3 || __builtin_popcount(rt) >= 3 ){
            ForceTile[t[i]][t[j]][t[k]][t[l]] = -1;
	    //printf("%d %d %d %d  =  %d\n", t[i], t[j], t[k], t[l], ForceTile[t[i]][t[j]][t[k]][t[l]]);//確認用
          }else if ( __builtin_popcount(wt) == 2 ){
            ForceTile[t[i]][t[j]][t[k]][t[l]] = wt;
	    //	                  printf("%d %d %d %d  =  %d\n", t[i], t[j], t[k], t[l], ForceTile[t[i]][t[j]][t[k]][t[l]]);//確認用
          }else if ( __builtin_popcount(rt) == 2 ) {
            ForceTile[t[i]][t[j]][t[k]][t[l]] = ~rt & 0x0f;
	    //         printf("%d %d %d %d  =  %d\n", t[i], t[j], t[k], t[l], ForceTile[t[i]][t[j]][t[k]][t[l]]); //確認用
          }        
	}
      }
    }
  }
  for(i = 0; i < 7; i++){
    for(j = 0; j < 7; j++){
      for(k = 0; k < 7; k++){
        for(l = 0; l < 7; l++){
          for(m = 1; m < 7; m++){
	    int ok = 1;
            if( t[i] && (t[i] & LEFT)  && ((t[m] & RIGHT)==0) ) ok = 0;
            if( t[i] && (~t[i] & LEFT)  && ((~t[m] & RIGHT)==0) ) ok = 0;
            if( t[j] && (t[j] & LOWER) && ((t[m] & UPPER)==0) ) ok = 0;
            if( t[j] && (~t[j] & LOWER) && ((~t[m] & UPPER)==0) ) ok = 0;
            if( t[k] && (t[k] & RIGHT) && ((t[m] & LEFT)==0 ) ) ok = 0;
            if( t[k] && (~t[k] & RIGHT) && ((~t[m] & LEFT)==0 ) ) ok = 0;
            if( t[l] && (t[l] & UPPER) && ((t[m] & LOWER)==0) ) ok = 0;
            if( t[l] && (~t[l] & UPPER) && ((~t[m] & LOWER)==0) ) ok = 0;
            PlaceableTile[t[i]][t[j]][t[k]][t[l]] |= ok << t[m];
	    //            printf("%d %d %d %d %d = %d\n", t[i], t[j], t[k], t[l], t[m], ok); //確認用
          }
        }
      }
    }
  }
}

int force_place(int x,int y, int tile, int bb[], int *bb_cnt){
  int t;

  board[x][y] = tile;           //配置できる場所ならタイルを配置
  hash ^= random_t[x][y][tile];   //ハッシュ値更新
  bb[(*bb_cnt)++] = (x << 10) | y; //配置した場所を記録


  int n = 10;

  
  loop_force[*bb_cnt-1][0]=x;
  loop_force[*bb_cnt-1][1]=y;

  if( board[x + 1][y] == BLANK ){ // 右強制手処理
    t = ForceTile[board[x + 2][y]][board[x + 1][y - 1]][board[x][y]][board[x + 1][y + 1]];
    if( t > 0 ) {
      force_flag = 1;
      t = force_place(x + 1, y, t, bb, bb_cnt);
    }
    if( t == -1 ) return -1; // 3 Same Color    
  }
  if( board[x][y - 1] == BLANK ){ // 上強制手処理
    t = ForceTile[board[x + 1][y - 1]][board[x][y - 2]][board[x - 1][y - 1]][board[x][y]];
    if( t > 0 ) {
      force_flag = 1;
      t  = force_place(x ,  y - 1, t, bb, bb_cnt); 
    }
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x - 1][y] == BLANK ){ // 左強制手処理
    t = ForceTile[board[x][y]][board[x - 1][y - 1]][board[x - 2][y]][board[x - 1][y + 1]];
    if( t > 0 ) {
      force_flag = 1;
      t = force_place(x - 1, y, t, bb, bb_cnt); 
    }
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x][y + 1] == BLANK ){ // 下強制手処理
    t = ForceTile[board[x + 1][y + 1]][board[x][y]][board[x - 1][y + 1]][board[x][y + 2]];
    if( t > 0 ) {
      force_flag = 1;
      t = force_place(x, y + 1, t, bb, bb_cnt);
    }
    if( t == -1 ) return -1; // 3 Same Color
  }



  return 0;
}



  
int sn_convert_place(char s[]){
  int i;
  int xx = 0;
  int yy = 0;
  char ss = '\0';
  int bb[256], bb_cnt;

  for(i = 0; i < strlen(s); i++) {
    ss = s[i];
    if (ss == '@') {
      xx = 0;
    }else if ('A' <= ss && ss <= 'Z') {
      xx *= 26;
      xx += ss - 'A' + 1;
    }else if ('0' <= ss && ss <= '9') {
      yy *= 10;
      yy += ss - '0';
    }else{
      break;
    }
  }
  int x = xx + x_min - 1;
  int y = yy + y_min - 1;

  if (ss == '\\'){
    if (place(x, y, UPPER_RIGHT_W, bb, &bb_cnt) == -1){
      if (place(x, y, LOWER_LEFT_W, bb, &bb_cnt) == -1){
        fprintf(stderr, "Can not place\n");
        //exit(0);
      }
    }
  }else if (ss == '/'){
    if (place(x, y, UPPER_LEFT_W, bb, &bb_cnt) == -1){
      if (place(x, y, LOWER_RIGHT_W, bb, &bb_cnt) == -1) {
        fprintf(stderr, "Can not place\n");
        //exit(0);
      }
    }
  }else if (ss == '+'){
    if (place(x, y, VERTICAL_W, bb, &bb_cnt) == -1){
      if (place(x, y, HORIZONTAL_W, bb, &bb_cnt) == -1) {
        fprintf(stderr, "Can not place\n");
        //exit(0);
      }
    }
  }else{
      fprintf(stderr, "Can not place\n");
  }

    return 0;
}



int loop_make(int x, int y, unsigned char tile, int n, int m){

  //printf("x = %d y = %d tile = %d n = %d m = %d \n", x, y, tile, n, m);

  int temp;
  int k=0,i;
 

  temp = 0x0f & ~tile;


  if(m==0) m++;
  else m--;

  if(force_flag==1){
    for(i=0; i<10; i++)
      if( (loop_end[i][0][m] == x && loop_end[i][1][m] == y) &&  (loop_start[i][0][m] == x && loop_start[i][1][m] == y)) return 0;
  }
  //  printf("temp=%d n = %d m = %d\n", temp, n, m);

  for(n = 0 ; n<20; n++) if(loop_end[n][0][m] == 0 && loop_start[n][0][m] == 0)break;

  
  loop_start_next[n][0][m] = x;
  loop_start_next[n][1][m] = y;
  loop_start[n][0][m] = x;
  loop_start[n][1][m] = y;
  loop_end_next[n][0][m] = x;
  loop_end_next[n][1][m] = y;
  loop_end[n][0][m] = x;
  loop_end[n][1][m] = y;


  if((temp & RIGHT) != 0) {temp -= RIGHT ;end[n][m] = LEFT; loop_end_next[n][0][m] = x + 1;} 
  else if((temp & LEFT) != 0) {temp -=LEFT; end[n][m] = RIGHT; loop_end_next[n][0][m] = x - 1;} 
  else if((temp & UPPER) != 0) {temp -= UPPER; end[n][m] = LOWER; loop_end_next[n][1][m] = y -1;}
  else if((temp & LOWER) != 0) {temp -= LOWER; end[n][m] = UPPER; loop_end_next[n][1][m] = y + 1;}
  
  if((temp & RIGHT) != 0) {start[n][m] = LEFT; loop_start_next[n][0][m] = x + 1;}
  else if((temp & LEFT) != 0) {start[n][m] = RIGHT; loop_start_next[n][0][m] = x - 1;}
  else if((temp & UPPER) != 0) {start[n][m] = LOWER; loop_start_next[n][1][m] = y - 1;}
  else if((temp & LOWER) != 0) {start[n][m] = UPPER; loop_start_next[n][1][m] = y + 1;}
  

  return n;
}


void Riichi(){
  int n, m;
  int x,y;

  riichi=-1;
  lost_check=-1;
 
  for(n=0; n<20; n++){
    for(m=0; m<2; m++){
      if(end[n][m] != 0 || start[n][m] != 0 ){
	
	if( abs(loop_end_next[n][0][m] - loop_start_next[n][0][m]) == 1 && loop_end_next[n][1][m] == loop_start_next[n][1][m]) {
	  riichi=m;
	  x=loop_end_next[n][0][m];
	  y=loop_end_next[n][1][m];
	}
	if(loop_end_next[n][0][m] == loop_start_next[n][0][m] && abs(loop_end_next[n][1][m] - loop_start_next[n][1][m]) == 1) {
	  riichi=m;
	  x=loop_end_next[n][0][m];
          y=loop_end_next[n][1][m];
	}

	if( abs(loop_end_next[n][0][m] - loop_start_next[n][0][m]) == 2 && loop_end_next[n][1][m] == loop_start_next[n][1][m] 
	    && loop_end[n][1][m] != loop_end_next[n][1][m] && loop_start[n][1][m] != loop_start_next[n][1][m] ) {
	  if(loop_end_next[n][0][m] > loop_start_next[n][0][m]){ x = loop_end_next[n][0][m]-1; y = loop_end_next[n][1][m]; }
	  else { x = loop_end_next[n][0][m]+1; y = loop_end_next[n][1][m]; }
	  if(board[x][y] == BLANK )riichi=m;
	}
	if( loop_end_next[n][0][m] == loop_start_next[n][0][m]  && abs(loop_end_next[n][1][m] - loop_start_next[n][1][m]) == 2
	    && loop_end[n][0][m] != loop_end_next[n][0][m] && loop_start[n][0][m] != loop_start_next[n][0][m] ) { 
	  if(loop_end_next[n][1][m] > loop_start_next[n][1][m]){x = loop_end_next[n][0][m]; y = loop_end_next[n][1][m]-1;}
	  else { x = loop_end_next[n][0][m]; y = loop_end_next[n][1][m]+1; }
	  if(board[x][y] == BLANK )riichi=m;
	}

	
	if( abs(loop_end_next[n][0][m] - loop_start_next[n][0][m]) == 2 && loop_end_next[n][1][m] == loop_start_next[n][1][m]
            && loop_end[n][0][m] != loop_start[n][0][m] && loop_end[n][1][m] != loop_start[n][0][m]  ){
	  
          if(loop_end_next[n][0][m] > loop_start_next[n][0][m]){ x = loop_end_next[n][0][m]-1; y = loop_end_next[n][1][m]; }
          else { x = loop_end_next[n][0][m]+1; y = loop_end_next[n][1][m]; }
          if(board[x][y] == BLANK )riichi=m;
        }
	
        if( loop_end_next[n][0][m] == loop_start_next[n][0][m]  && abs(loop_end_next[n][1][m] - loop_start_next[n][1][m]) == 2
	    && loop_end[n][0][m] != loop_start[n][0][m] && loop_end[n][1][m] != loop_start[n][0][m]  ){
	  
          if(loop_end_next[n][1][m] > loop_start_next[n][1][m]){x = loop_end_next[n][0][m]; y = loop_end_next[n][1][m]-1;}
          else { x = loop_end_next[n][0][m]; y = loop_end_next[n][1][m]+1; }
	  if(board[x][y] == BLANK )riichi=m;
	  }
	
	if( abs(loop_end_next[n][0][m] - loop_start_next[n][0][m]) > 7 || abs(loop_end_next[n][1][m] - loop_start_next[n][1][m]) > 7) riichi = m;

	if(riichi != -1){
	  if(lost_check ==-1) lost_check = riichi;
	  else if( lost_check != riichi ) lost_check = -2;
	}
      }
    }
  }
  


  //if( riichi !=-1 )printf("リーチが見つかりました. x=%d, y=%d\n",x,y);

}

int line(int x, int y){

  int i, n, m;
  int n1=-1, m1=-1, n2=-1, m2=-1, end_start1, end_start2; //endとstart両方につながる場合に使う 
  int vect_flag=0;
  int change=0;
  unsigned char tile_bit;
  int mm=-1;
  int vect_cnt=0;
  int win=-1;
  int vect_color=-1;//endとstartの両方が既存タイルにつながる色を保持
  int vect_red = 0;
  int vect_white = 0;

  

  if(loop_win != -1) win = loop_win; 
    
  for(n=0; n<20; n++){
    tile_bit = board[x][y];
    for(m=0; m<2; m++){
      if(end[n][m] != 0 || start[n][m] != 0 ){
	if(m==1) tile_bit = 0x0f & ~tile_bit;      
	if( loop_end_next[n][0][m] == x && loop_end_next[n][1][m] == y && (end[n][m] & tile_bit) != 0){
	  if( (mm == 1 && m == 0) || (mm == 0 && m == 1) )  mm = -2; // 赤、白どちらも既存のタイルにつながる場合
	  else mm = m;
	  loop_win=1;
	  if(m==0) vect_red++;
	  else vect_white++;
	}
	if( loop_start_next[n][0][m] == x && loop_start_next[n][1][m] == y && (start[n][m] & tile_bit) != 0 ){
	  if( (mm == 1 && m == 0) || (mm == 0 && m == 1) ) mm = -2;
	  else mm = m;
	  if(m==0) vect_red++;
	  else vect_white++;
	  if(loop_win==1){
	    //printf("ループが見つかりました。x=%d y=%d mm=%d\n",x,y,mm);
	    loop_win = mm; return 0;
	  }
	}
	loop_win=-1;
      }
    }
  }

  

  if(win != -1){
    loop_win = win;
  }

  if( mm==-2 ) {
    if( vect_red==2 || vect_white==2 ) mm = -1;
  }

  vect_cnt = vect_red + vect_white;
  if( vect_red == 2 ) vect_color = 0;
  else if( vect_white == 2 ) vect_color = 1;

  //printf("mm=%d\n",mm);
  
  if(mm == -2 && vect_cnt!=3 ){//置いたタイルの赤、白どちらのラインもendかstartの片方に既存のタイルがつながる場合
    for(n=0; n<20; n++){
      tile_bit = board[x][y];
      for(m=0; m<2; m++){
	if(loop_start[n][0][m] != 0 || loop_end[n][0][m] != 0){
	  if(m==1) tile_bit = 0x0f & ~tile_bit;
	  if( loop_end_next[n][0][m] == x && loop_end_next[n][1][m] == y && (end[n][m] & tile_bit) != 0){
	    change = tile_bit - end[n][m];
	    loop_end[n][0][m] =x;
	    loop_end[n][1][m]= y;
	    if(change == RIGHT){ end[n][m] = LEFT; loop_end_next[n][0][m] += 1; }
	    else if(change == LEFT){ end[n][m] = RIGHT; loop_end_next[n][0][m] -= 1; }
	    else if(change == UPPER){ end[n][m] = LOWER; loop_end_next[n][1][m] -= 1; }
	    else if(change == LOWER){ end[n][m] = UPPER; loop_end_next[n][1][m] += 1; }
	  }else if( loop_start_next[n][0][m] == x && loop_start_next[n][1][m] == y && (start[n][m] & tile_bit) != 0 ){
	    change = tile_bit - start[n][m];
	    loop_start[n][0][m]=x;
	    loop_start[n][1][m]= y;
	    if(change == RIGHT){ start[n][m] = LEFT; loop_start_next[n][0][m] += 1; }
	    else if(change == LEFT){ start[n][m] = RIGHT; loop_start_next[n][0][m] -= 1; }
	    else if(change == UPPER){ start[n][m] = LOWER; loop_start_next[n][1][m] -= 1; }
	    else if(change == LOWER){ start[n][m] = UPPER; loop_start_next[n][1][m] += 1; }
	  }
	}
      }
    }
  }
  
  
  if(mm!=-2 && vect_cnt > 0){
    for(n=0; n<20; n++){
      tile_bit = board[x][y];
      for(m=0; m<2; m++){
	if(loop_start[n][0][m] != 0 || loop_end[n][0][m] != 0){
	  if(m==1) tile_bit = 0x0f & ~tile_bit;
	  if( loop_end_next[n][0][m] == x && loop_end_next[n][1][m] == y && (end[n][m] & tile_bit) != 0){
	    change = tile_bit - end[n][m];
	    loop_end[n][0][m] =x;
            loop_end[n][1][m]= y;

	    if( vect_flag==0 && vect_cnt!=3 ){ //赤または白のどちらかがend start両方に既存タイルがつながり、片方の色のラインが新しくできる場合
	      loop_make(x, y, tile_bit, n, m);
	      n1=n; m1=m, end_start1=0;
	    }else if ( vect_color == m && n1 == -1 && m1 == -1 ){ n1=n; m1=m; end_start1=0; }
	    else if( vect_color == m && n2 == -1 && m2 == -1 ){ n2=n; m2=m; end_start2=0; }

	    if(change == RIGHT){ end[n][m] = LEFT; loop_end_next[n][0][m] += 1; }
	    else if(change == LEFT){ end[n][m] = RIGHT; loop_end_next[n][0][m] -= 1;}
	    else if(change == UPPER){ end[n][m] = LOWER; loop_end_next[n][1][m] -= 1; }
	    else if(change == LOWER){ end[n][m] = UPPER; loop_end_next[n][1][m] += 1; }
	    vect_flag++;
	  }else if( loop_start_next[n][0][m] == x && loop_start_next[n][1][m] == y && (start[n][m] & tile_bit) != 0 ){
	    change = tile_bit - start[n][m];
	    loop_start[n][0][m]=x;
            loop_start[n][1][m]= y;

	    if( vect_flag==0 && vect_cnt!=3 ){
	      loop_make(x, y, tile_bit, n , m);
	      n1=n; m1=m; end_start1=1; 
	    }else if ( vect_color == m && n1 == -1 && m1 == -1 ) { n1=n; m1=m; end_start1=1;}
	    else if( vect_color == m && n2 == -1 && m2 == -1 ){ n2=n; m2=m; end_start2=1; }

	    if(change == RIGHT){ start[n][m] = LEFT; loop_start_next[n][0][m] += 1; }
	    else if(change == LEFT){ start[n][m] = RIGHT; loop_start_next[n][0][m] -= 1;}
	    else if(change == UPPER){ start[n][m] = LOWER; loop_start_next[n][1][m] -= 1; }
	    else if(change == LOWER){ start[n][m] = UPPER; loop_start_next[n][1][m] += 1; }
	    vect_flag++;
	  }
	}
      }
    }
    
  
    
    if(vect_flag>=2){//赤または白のラインのstart,end双方向にタイルがつながる場合
      if(end_start1==0){
	if(end_start2==0){
	  loop_end_next[n1][0][m1] = loop_start_next[n2][0][m2];
	  loop_end_next[n1][1][m1] = loop_start_next[n2][1][m2];
	  loop_end[n1][0][m1] = loop_start[n2][0][m2];
	  loop_end[n1][1][m1] = loop_start[n2][1][m2];
	  end[n1][m1] = start[n2][m2];
	}else if(end_start2==1){
	  loop_end_next[n1][0][m1] = loop_end_next[n2][0][m2];
	  loop_end_next[n1][1][m1] = loop_end_next[n2][1][m2];
	  loop_end[n1][0][m1] = loop_end[n2][0][m2];
	  loop_end[n1][1][m1] = loop_end[n2][1][m2];
	  end[n1][m1] = end[n2][m2];
	}

      }else if(end_start1==1){ 
	 if(end_start2==0){
	   loop_start_next[n1][0][m1] = loop_start_next[n2][0][m2];
	   loop_start_next[n1][1][m1] = loop_start_next[n2][1][m2];
	   loop_start[n1][0][m1] = loop_start[n2][0][m2];
	   loop_start[n1][1][m1] = loop_start[n2][1][m2];
	   start[n1][m1] = start[n2][m2];
	 }else if(end_start2==1){
	   loop_start_next[n1][0][m1] = loop_end_next[n2][0][m2];
	   loop_start_next[n1][1][m1] = loop_end_next[n2][1][m2];
	   loop_start[n1][0][m1] = loop_end[n2][0][m2];
           loop_start[n1][1][m1] = loop_end[n2][1][m2];
           start[n1][m1] = end[n2][m2];
	 }

       }
       loop_start[n2][0][m2]=0;
       loop_start[n2][1][m2]=0;
       loop_end[n2][0][m2]=0;
       loop_end[n2][1][m2]=0;
       loop_start_next[n2][0][m2]=0;
       loop_start_next[n2][1][m2]=0;
       loop_end_next[n2][0][m2]=0;
       loop_end_next[n2][1][m2]=0;
       start[n2][m2] = 0;
       end[n2][m2] = 0;
     }
  }


  if(vect_flag == 0 && mm==-1){ //4方向にタイルがなく新しく2本のライン情報を記録する場合
    
    for(n=0; n<20; n++) if((loop_end[n][0][0] == 0 && loop_start[n][0][0] == 0) && (loop_end[n][0][1] == 0 && loop_start[n][0][1]==0) ) break; //空いている配列を探す
    
    for(m=0; m<2; m++){
      loop_start[n][0][m]=x;
      loop_start[n][1][m]=y;
      loop_end[n][0][m]=x;
      loop_end[n][1][m]= y;
    }
    
    if( board[x][y] == VERTICAL_W){
      loop_end_next[n][0][0] = x;
      loop_end_next[n][1][0] = y-1;
      loop_start_next[n][0][0] = x;
      loop_start_next[n][1][0] = y+1;
      loop_end_next[n][0][1] = x-1;
      loop_end_next[n][1][1] = y;
      loop_start_next[n][0][1] = x+1;
      loop_start_next[n][1][1] = y;
      end[n][0] = LOWER;
      start[n][0] = UPPER;
      end[n][1] = RIGHT;
      start[n][1] = LEFT;
    }else if(board[x][y] == HORIZONTAL_W){
      loop_end_next[n][0][0] = x-1;
      loop_end_next[n][1][0] = y;
      loop_start_next[n][0][0] = x+1;
      loop_start_next[n][1][0] = y;
      loop_end_next[n][0][1] = x;
      loop_end_next[n][1][1] = y-1;
      loop_start_next[n][0][1] = x;
      loop_start_next[n][1][1] = y+1;
      end[n][0] = RIGHT;
      start[n][0] = LEFT;
      end[n][1] = LOWER;
      start[n][1] = UPPER;
    }else if(board[x][y] == UPPER_LEFT_W){
      loop_end_next[n][0][0] = x;
      loop_end_next[n][1][0] = y-1;
      loop_start_next[n][0][0] = x-1;
      loop_start_next[n][1][0] = y;
      loop_end_next[n][0][1] = x+1;
      loop_end_next[n][1][1] = y;
      loop_start_next[n][0][1] = x;
      loop_start_next[n][1][1] = y+1;
      end[n][0] = LOWER;
      start[n][0] = RIGHT;
      end[n][1] = LEFT;
      start[n][1] = UPPER;
    }else if(board[x][y] == LOWER_RIGHT_W){
      loop_end_next[n][0][0] = x+1;
      loop_end_next[n][1][0] = y;
      loop_start_next[n][0][0] = x;
      loop_start_next[n][1][0] = y+1;
      loop_end_next[n][0][1] = x;
      loop_end_next[n][1][1] = y-1;
      loop_start_next[n][0][1] = x-1;
      loop_start_next[n][1][1] = y;
      end[n][0] = LEFT;
      start[n][0] = UPPER;
      end[n][1] = LOWER;
      start[n][1] = RIGHT;
    }else if(board[x][y] == UPPER_RIGHT_W){
      loop_end_next[n][0][0] = x;
      loop_end_next[n][1][0] = y-1;
      loop_start_next[n][0][0] = x+1;
      loop_start_next[n][1][0] = y;
      loop_end_next[n][0][1] = x-1;
      loop_end_next[n][1][1] = y;
      loop_start_next[n][0][1] = x;
      loop_start_next[n][1][1] = y+1;
      end[n][0] = LOWER;
      start[n][0] = LEFT;
      end[n][1] = RIGHT;
      start[n][1] = UPPER;
    }else if(board[x][y] == LOWER_LEFT_W){
      loop_end_next[n][0][0] = x;
      loop_end_next[n][1][0] = y+1;
      loop_start_next[n][0][0] = x-1;
      loop_start_next[n][1][0] = y;
      loop_end_next[n][0][1] = x+1;
      loop_end_next[n][1][1] = y;
      loop_start_next[n][0][1] = x;
      loop_start_next[n][1][1] = y-1;
      end[n][0] = UPPER;
      start[n][0] = RIGHT;
      end[n][1] = LEFT;
      start[n][1] = LOWER;
    }
  }
  
  return 0;

}

int place(int x, int y, int tile, int bb[], int *bb_cnt)
{
  int i;
  int hash_orig = hash;
  int n=0,m=0;
  int change = 0;
  int next = 0;
  unsigned char tile_bit;
  int nn;
  int cnt=0;
  int xx=0,yy=0;
    
  for(i=0; i<10; i++){
    loop_force[i][0] = 0;
    loop_force[i][1] = 0;
   }
  force_flag = 0;
  
  loop_win = -1;
  riichi = -1;


  if( board[x][y] != BLANK ) return -1;
  if( PlaceableTile[board[x + 1][y]][board[x][y - 1]][board[x - 1][y]][board[x][y + 1]] & (1 << tile) ){
    *bb_cnt = 0;
    if( force_place(x, y, tile, bb, bb_cnt) == -1 ){ // 3 Same Color
      for(i = 0; i < *bb_cnt; i++) board[bb[i] >> 10][bb[i] & 0x3ff] = 0;
      *bb_cnt = 0;
      hash = hash_orig;
      return -1; // 3 Same Color
    }
    if( x < x_min ) x_min = x;
    else if( x > x_max ) x_max = x;
    if( y < y_min ) y_min = y;
    else if( y > y_max ) y_max = y;




    tile_bit = tile;
    //printf("tile = %d UPPER = %d LOWER = %d LEFT = %d RIGHT = %d\n",tile_bit, tile_bit & UPPER, tile_bit & LOWER, tile_bit & LEFT, tile_bit & RIGHT);

    if(x==257&&y==257){

      fprintf(stderr, "\n\n");
      for(n=0;n<20;n++){
	if(end[n][0] != 0 ||  start[n][0] != 0 || end[n][1] != 0 || start[n][1] != 0){
	  fprintf(stderr, "\nend_red=%d  start_red=%d end_white=%d start_white=%d\n", end[n][0], start[n][0], end[n][1], start[n][1]);
	  for(m=0; m<2; m++) {
	    fprintf(stderr, "loop_end[%d][x][%d] = %d loop_start[%d][x][%d] = %d end_next[%d][x][%d]=%d start_next[%d][x][%d]=%d\n",
		    n, m, loop_end[n][0][m], n, m, loop_start[n][0][m], n, m, loop_end_next[n][0][m], n, m, loop_start_next[n][0][m]);
	    fprintf(stderr, "loop_end[%d][y][%d] = %d loop_start[%d][y][%d] = %d end_next[%d][y][%d]=%d start_next[%d][y][%d]=%d\n",
		    n, m, loop_end[n][1][m], n, m, loop_start[n][1][m] , n, m, loop_end_next[n][1][m], n, m, loop_start_next[n][1][m]);
	  }
	}
      }
    }


    if(force_flag==1){//強制手が発生する場合

      for(nn=0; nn<10; nn++){
	if(loop_force[nn][0] != 0)
        line(loop_force[nn][0], loop_force[nn][1]);
      }


    }else{//強制手が発生しない場合

      //片方か双方かをチェック
      if(board[x-1][y])cnt++;
      if(board[x+1][y])cnt++;
      if(board[x][y-1])cnt++;
      if(board[x][y+1])cnt++;

     
      for(n=0; n<20; n++){
	tile_bit = tile;
	for(m=0; m<2; m++){
	  if(loop_start[n][0][m] != 0 || loop_end[n][0][m] != 0){
	    if(m==1) tile_bit = 0x0f & ~tile_bit; //白のラインを見る場合はタイルのビットを反転する
	    if( loop_end_next[n][0][m] == x && loop_end_next[n][1][m] == y && (end[n][m] & tile_bit) != 0){
	      change = tile_bit - end[n][m];
	      if(change == RIGHT){ end[n][m] = LEFT; loop_end_next[n][0][m] += 1; }
	      else if(change == LEFT){ end[n][m] = RIGHT; loop_end_next[n][0][m] -= 1; }
	      else if(change == UPPER){ end[n][m] = LOWER; loop_end_next[n][1][m] -= 1; }
	      else if(change == LOWER){ end[n][m] = UPPER; loop_end_next[n][1][m] += 1; }
	      loop_end[n][0][m] =x;
	      loop_end[n][1][m]= y;
	      if(cnt==1) loop_make(x, y, tile_bit, n, m); //片方向に繋がる場合のみ新しくラインを記憶する
	    }else if( loop_start_next[n][0][m] == x && loop_start_next[n][1][m] == y && (start[n][m] & tile_bit) != 0 ){
	      change = tile_bit - start[n][m];
	      if(change == RIGHT){ start[n][m] = LEFT; loop_start_next[n][0][m] += 1; }
	      else if(change == LEFT){ start[n][m] = RIGHT; loop_start_next[n][0][m] -= 1; }
	      else if(change == UPPER){ start[n][m] = LOWER; loop_start_next[n][1][m] -= 1; }
	      else if(change == LOWER){ start[n][m] = UPPER; loop_start_next[n][1][m] += 1; }
	      loop_start[n][0][m]=x;
	      loop_start[n][1][m]= y;
	      if(cnt==1) loop_make(x, y, tile_bit, n , m);
	    }
	  }
	}
      }

    }
     
    
    /*  
    for(n=0;n<20;n++){
      if(end[n][0] != 0 ||  start[n][0] != 0 || end[n][1] != 0 || start[n][1] != 0){
        printf("\nend_red=%d  start_red=%d end_white=%d start_white=%d\n", end[n][0], start[n][0], end[n][1], start[n][1]);
        for(m=0; m<2; m++) {
          printf("loop_end[%d][x][%d] = %d loop_start[%d][x][%d] = %d end_next[%d][x][%d]=%d start_next[%d][x][%d]=%d\n",
                 n, m, loop_end[n][0][m], n, m, loop_start[n][0][m], n, m, loop_end_next[n][0][m], n, m, loop_start_next[n][0][m]);
          printf("loop_end[%d][y][%d] = %d loop_start[%d][y][%d] = %d end_next[%d][y][%d]=%d start_next[%d][y][%d]=%d\n",
                 n, m, loop_end[n][1][m], n, m, loop_start[n][1][m] , n, m, loop_end_next[n][1][m], n, m, loop_start_next[n][1][m]);
        }
      }
      }
    */
    
    /*
    for(n=0; n<20; n++){
      for(m=0; m<2; m++){
	if(end[n][m] != 0 || start[n][m] != 0 ){
	  if( abs(loop_end_next[n][0][m] - loop_start_next[n][0][m]) > 8 || abs(loop_end_next[n][1][m] - loop_start_next[n][1][m]) > 8)
	    //printf("ビクトリーラインができました。 N=%d M=%d\n", n, m);
	    loop_win = m;
	}
      }
      }*/
    
    Riichi();

    return 1;
  }
  return -1;
}

void xxyyt_to_string(int xx, int yy, int t, char s[])
{
  int s_cnt = 0;

  if (xx == 0){
    s[s_cnt++] = '@';
  }else if(xx <= 26){
    s[s_cnt++] = 'A' + xx - 1;
  }else{
    s[s_cnt++] = 'A' + ((xx-1)/26) - 1;
    s[s_cnt++] = 'A' + ((xx-1)%26);
  }
  sprintf(&s[s_cnt],"%d", yy);
  if (t == VERTICAL_W || t == HORIZONTAL_W) sprintf(&s[s_cnt],"%d+", yy);
  else if (t == UPPER_LEFT_W || t == LOWER_RIGHT_W) sprintf(&s[s_cnt],"%d/", yy);
  else sprintf(&s[s_cnt],"%d\\", yy);
}


int yrsearch(int *rx, int *ry, int *rt, int color, int depth){
  int i, j, x, y, t, ret;
  int fin=0;
  int x_min_backup = x_min;
  int x_max_backup = x_max;
  int y_min_backup = y_min;
  int y_max_backup = y_max;
  int bb[10000], bb_cnt;
  unsigned long long hash_backup = hash;
  int p_cnt = 0;

  int n, m;

  int loop_start_backup[loop_number][2][2];
  int loop_start_next_backup[loop_number][2][2];
  int start_backup[loop_number][2];
  int loop_end_backup[loop_number][2][2];
  int loop_end_next_backup[loop_number][2][2];
  int end_backup[loop_number][2];

  
  /*
  //ハッシュの利用
  if( HASH_TBL[hash & HASHWIDTH] == ( hash | (color-1) ) ){
    return WINLOSS[hash & HASHWIDTH];
    }
  */
  //キラームーブチェック
  x = killer_x[depth];
  y = killer_y[depth];
  t = killer_t[depth];

  for(n=0;n<20;n++){
    end_backup[n][0] = end[n][0];
    end_backup[n][1] = end[n][1];
    start_backup[n][0] = start[n][0];
    start_backup[n][1] = start[n][1];
    for(m=0; m<2; m++) {
      loop_end_backup[n][0][m] = loop_end[n][0][m];
      loop_end_backup[n][1][m] = loop_end[n][1][m];
      loop_start_backup[n][0][m] = loop_start[n][0][m];
      loop_start_backup[n][1][m] = loop_start[n][1][m];
      loop_end_next_backup[n][0][m] = loop_end_next[n][0][m];
      loop_end_next_backup[n][1][m] = loop_end_next[n][1][m];
      loop_start_next_backup[n][0][m] = loop_start_next[n][0][m];
      loop_start_next_backup[n][1][m] = loop_start_next[n][1][m];
    }
  }


  if( board[x][y] == BLANK ){
    if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
      if( place(x, y, t, bb, &bb_cnt ) == 1 ){
	if( loop_win == color-1 ){ // 自分のループができた
	  fin = 1;
	}else{
	  if( depth < max_depth ){
	    int flag = 0;
	    if( loop_win == 2-color ){ // 相手のループができた
	      flag = 1;
	    }
	    if( flag==0 ){
	      int ret;
	      int _rx, _ry, _rt;
	      ret = search( &_rx, &_ry, &_rt, 3-color, depth+1 );
	      if( ret == color ){
		fin = 1; //自分が勝つ
	      }
	    }
	  }
	}
	for( j=0; j<bb_cnt; j++) board[bb[j] >> 10][bb[j] & 0x3ff] = 0;
	hash = hash_backup;
	x_min = x_min_backup;
	x_max = x_max_backup;
	y_min = y_min_backup;
	y_max = y_max_backup;
	for(n=0;n<20;n++){
	  end[n][0] = end_backup[n][0];
	  end[n][1] = end_backup[n][1];
	  start[n][0] = start_backup[n][0];
	  start[n][1] = start_backup[n][1];
	  for(m=0; m<2; m++) {
	    loop_end[n][0][m] = loop_end_backup[n][0][m];
	    loop_end[n][1][m] = loop_end_backup[n][1][m];
	    loop_start[n][0][m] = loop_start_backup[n][0][m];
	    loop_start[n][1][m] = loop_start_backup[n][1][m];
	    loop_end_next[n][0][m] = loop_end_next_backup[n][0][m];
	    loop_end_next[n][1][m] = loop_end_next_backup[n][1][m];
	    loop_start_next[n][0][m] = loop_start_next_backup[n][0][m];
	    loop_start_next[n][1][m] = loop_start_next_backup[n][1][m];
	  }
	}

	if( fin == 1 ){
	  return color;
	}
      }
    }
  }

  


  for( y=y_min-1; y<=y_max+1; y++){
    for( x=x_min-1; x<=x_max+1; x++){
      if( board[x][y] ) continue;
      if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
	if( depth==2 ){
	  if( x==x_min-1 ) fprintf(stderr, " d=%d %d %d @%d", depth, x, y, y-y_min+1);
	  else fprintf(stderr, " d=%d %d %d %c%d", depth, x, y, x-x_min+'A', y-y_min+1);
	}
	for( i=0; i<6; i++){
	  t = TLIST[i];
	  if( place( x, y, t, bb, &bb_cnt ) == 1 ){
	    if( loop_win == color-1 ){ //自分のループができた
 	      killer_x[depth] = x; killer_y[depth] = y; killer_t[depth] = t;
	      fin = 1;
	    }else{ // 相手のループを確認
	      int flag = 0;
	      if( loop_win == 2-color ){
		flag = 1;
	      }
	      if( flag == 0 ){
		if( depth < max_depth ){
		  int ret;
		  int _rx, _ry, _rt;
		  ret = search(&_rx, &_ry, &_rt, 3-color, depth + 1);
		  if( ret == color ){
		    if( depth == 2 ) fprintf(stderr, "%c(K) ", mark[t]);
		    killer_x[depth] = x; killer_y[depth] = y; killer_t[depth] = t;
		    fin = 1;//自分が勝つ
		  }else if( ret == 3-color ){
		    if( depth==2 ) fprintf(stderr, "%c(M) ", mark[t]);
		    //何もしない
		  }else{
		    if( depth==2 ) fprintf(stderr, " %c ", mark[t]);
		    p_cnt++;
		  }
		}else{ //末端(depth == max_depth)
		  if( depth==2 ) fprintf(stderr, " %c ", mark[t]);
		  p_cnt++;
		}
	      }else{
		if( depth==2 ) fprintf(stderr, " %c(M) ", mark[t]);
	      }
	    }
	    for( j=0; j<bb_cnt; j++ ) board[bb[j] >> 10][bb[j] & 0x3ff] = 0;
	    hash = hash_backup;
	    x_min = x_min_backup; x_max = x_max_backup;
	    y_min = y_min_backup; y_max = y_max_backup;
	    for(n=0;n<20;n++){
	      end[n][0] = end_backup[n][0];
	      end[n][1] = end_backup[n][1];
	      start[n][0] = start_backup[n][0];
	      start[n][1] = start_backup[n][1];
	      for(m=0; m<2; m++) {
		loop_end[n][0][m] = loop_end_backup[n][0][m];
		loop_end[n][1][m] = loop_end_backup[n][1][m];
		loop_start[n][0][m] = loop_start_backup[n][0][m];
		loop_start[n][1][m] = loop_start_backup[n][1][m];
		loop_end_next[n][0][m] = loop_end_next_backup[n][0][m];
		loop_end_next[n][1][m] = loop_end_next_backup[n][1][m];
		loop_start_next[n][0][m] = loop_start_next_backup[n][0][m];
		loop_start_next[n][1][m] = loop_start_next_backup[n][1][m];
	      }
	    }

	    if( fin == 1 ){
	      *rx = x;
	      *ry = y;
	      *rt = t;
	      return color;
	    }
	  }
	}
      }
    }
  }
  if( p_cnt == 0 ) {
      HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
      WINLOSS[hash & HASHWIDTH] = 3 - color; //ハッシュ登録
      hash_cnt++;
      return 3 - color;
 }
return 0;
}

int search(int *rx, int *ry, int *rt, int color, int depth){
  int i, j, x, y, t, ret;
  int fin = 0;
  int x_min_backup = x_min;
  int x_max_backup = x_max;
  int y_min_backup = y_min;
  int y_max_backup = y_max;
  int bb[10000], bb_cnt;
  unsigned long long hash_backup = hash;
  int px[10000], py[10000], pt[10000];
  int p_cnt=0;

  int n, m;

  int loop_start_backup[loop_number][2][2];
  int loop_start_next_backup[loop_number][2][2];
  int start_backup[loop_number][2];
  int loop_end_backup[loop_number][2][2];
  int loop_end_next_backup[loop_number][2][2];
  int end_backup[loop_number][2];




  for(n=0;n<20;n++){
      end_backup[n][0] = end[n][0];
      end_backup[n][1] = end[n][1];
      start_backup[n][0] = start[n][0];
      start_backup[n][1] = start[n][1];      
      for(m=0; m<2; m++) {
	loop_end_backup[n][0][m] = loop_end[n][0][m];
	loop_end_backup[n][1][m] = loop_end[n][1][m];
	loop_start_backup[n][0][m] = loop_start[n][0][m];
	loop_start_backup[n][1][m] = loop_start[n][1][m];
	loop_end_next_backup[n][0][m] = loop_end_next[n][0][m];
	loop_end_next_backup[n][1][m] = loop_end_next[n][1][m];
	loop_start_next_backup[n][0][m] = loop_start_next[n][0][m];
	loop_start_next_backup[n][1][m] = loop_start_next[n][1][m];
      }
  }
  
  /*
  //ハッシュの利用
  if( depth > 1){
    if (HASH_TBL[hash & HASHWIDTH] == (hash | (color -1))){
      return WINLOSS[hash & HASHWIDTH]; //ハッシュ登録済み
    }
    }*/
  
  
  if( depth > 1 ){
    x = killer_x[depth];
    y = killer_y[depth];
    t = killer_t[depth];
    if(board[x][y] == BLANK){
      if(board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1]){
	if( place(x, y, t, bb, &bb_cnt) == 1 ){
	  //	  fprintf(stderr, "win=%d", loop_win);
	  if( loop_win == color-1 ){ //自分のloopができた
	    fin = 1;
	  }else{
	    if( depth < max_depth ){
	      int flag=0;
	      if( loop_win == 2-color  ){
		flag = 1;// 相手のループができた
	      }
	      if(flag == 0){ //相手のループはできていない
		int ret;
		int _rx, _ry, _rt;
		ret = yrsearch(&_rx, &_ry, &_rt, 3-color, depth + 1);
		if(ret == color ){
		  fin = 1; //自分が勝つ
		}
	      }
	    }
	  }
	  for(j = 0; j < bb_cnt; j++) board[bb[j] >> 10][bb[j] & 0x3ff] = 0;
	  hash = hash_backup;
          x_min = x_min_backup;
          x_max = x_max_backup;
          y_min = y_min_backup;
          y_max = y_max_backup;
	  for(n=0;n<20;n++){
	    end[n][0] = end_backup[n][0];
	    end[n][1] = end_backup[n][1];
	    start[n][0] = start_backup[n][0];
	    start[n][1] = start_backup[n][1];
	    for(m=0; m<2; m++) {
	      loop_end[n][0][m] = loop_end_backup[n][0][m];
	      loop_end[n][1][m] = loop_end_backup[n][1][m];
	      loop_start[n][0][m] = loop_start_backup[n][0][m];
	      loop_start[n][1][m] = loop_start_backup[n][1][m];
	      loop_end_next[n][0][m] = loop_end_next_backup[n][0][m];
	      loop_end_next[n][1][m] = loop_end_next_backup[n][1][m];
	      loop_start_next[n][0][m] = loop_start_next_backup[n][0][m];
	      loop_start_next[n][1][m] = loop_start_next_backup[n][1][m];
	    }
	  }
	  if( fin == 1 ) {
	    return color;
          }
	}
      }
    }
  }

  for( y=y_min -1; y<=y_max+1; y++ ){
    for (x=x_min-1; x<=x_max+1; x++ ){
      if( board[x][y] ) continue;
      if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
	if( depth == 1 ){
	  if( x == x_min-1 ) fprintf(stderr, "d=%d %d %d @%d", depth, x, y, y-y_min+1);
	  else fprintf(stderr, "d=%d %d %d %c%d", depth, x, y, x-x_min + 'A', y-y_min+1);
	}
	for(i=0; i<6; i++){
	  t = TLIST[i];
	  if( place(x, y, t, bb, &bb_cnt) == 1 ){
	    if(loop_win == color-1){
	      if(depth==1) fprintf(stderr, "%c %s-LoopOrLine", mark[t], color_s[color]);
	      killer_x[depth] = x; killer_y[depth] = y; killer_t[depth] = t;
	      fin=1;
	    }else{
	      int flag=0;
	      if(loop_win == 2- color){
		flag = 1;
	      }
	      if( flag == 0 && riichi==-1 ){
		//相手のループはできていないしリーチもしていないから読まない
	      }else if( flag==0 && riichi == color-1 && lost_check != -2){ //相手のループはできていない。自分がリーチ状態
		if( depth<max_depth ){
		  int ret;
		  int _rx, _ry, _rt;
		  ret = yrsearch(&_rx, &_ry, &_rt, 3 - color, depth + 1);
		  if( ret == color ){
		    if( depth == 1 ){
		      fprintf(stderr, "%c(**KACHI**)", mark[t]);
		    }
		    killer_x[depth] = x; killer_y[depth] = y; killer_t[depth] = t;
		    fin = 1; //自分が勝つ
		  }else if( ret == 3-color ){ //相手が勝つ
		    if( depth==1 ) {
		      fprintf(stderr, "%c(L)", mark[t]);
		    }

		  }else{ //勝敗がつかない
		    if( depth==1 ){
		      if( riichi == color-1 ) fprintf(stderr, " %c(R)", mark[t]);
		      else fprintf(stderr, " %c", mark[t]);
		      if( riichi == color-1) px[p_cnt] = x; py[p_cnt] = y; pt[p_cnt] = t;
		    }
		    p_cnt++;
		  }
		}else{ //末端(depth==max_depth)
		  if( depth==1 ){ //MAX_DEPTH と depthの両方とも1のとき
		    if( riichi == color-1)  fprintf(stderr, " %c(R)", mark[t]);
		    else fprintf(stderr, " %c", mark[t]);
		    if( riichi == color-1) {
		      px[p_cnt]=x; py[p_cnt]=y; pt[p_cnt]=t;
		    }
		  }
		  p_cnt++;
		}
	      }else{ //相手のループができて負け
		if( depth==1 ) fprintf(stderr, " %c(L)", mark[t]);
	      }
	    }
	    for( j=0; j<bb_cnt; j++) board[bb[j] >> 10][bb[j] & 0x3ff] = 0;
	    hash = hash_backup;
	    x_min = x_min_backup; x_max = x_max_backup;
	    y_min = y_min_backup; y_max = y_max_backup;

	    for(n=0;n<20;n++){
	      end[n][0] = end_backup[n][0];
	      end[n][1] = end_backup[n][1];
	      start[n][0] = start_backup[n][0];
	      start[n][1] = start_backup[n][1];
	      for(m=0; m<2; m++) {
		loop_end[n][0][m] = loop_end_backup[n][0][m];
		loop_end[n][1][m] = loop_end_backup[n][1][m];
		loop_start[n][0][m] = loop_start_backup[n][0][m];
		loop_start[n][1][m] = loop_start_backup[n][1][m];
		loop_end_next[n][0][m] = loop_end_next_backup[n][0][m];
		loop_end_next[n][1][m] = loop_end_next_backup[n][1][m];
		loop_start_next[n][0][m] = loop_start_next_backup[n][0][m];
		loop_start_next[n][1][m] = loop_start_next_backup[n][1][m];
	      }
	    }


	    if( fin == 1 ){
	      HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
	      WINLOSS[hash & HASHWIDTH] = color; //ハッシュ登録
	      hash_cnt++;
	      *rx = x;
	      *ry = y;
	      *rt = t;
	      if( depth==1 ) fprintf(stderr, "\n");
	      return color;
	    }
	  }
	}
	if( depth==1 ) fprintf(stderr, "\n");
      }
    }
  }
  if( p_cnt==0 ){
    return 3-color;
  }
  if( depth==1 ){
    int r = random() % p_cnt;
    *rx = px[r];
    *ry = py[r];
    *rt = pt[r];
  }
  return 0;
}


int search_place(int turn, char s[], int color){

  int x,y,t;
  int x_min_backup = x_min;
  int y_min_backup = y_min;
  int ret;
  int bb[256], bb_cnt;

  
  for(max_depth = 1; max_depth <= MAX_DEPTH; max_depth += 2){
  //  for(max_depth = 1; max_depth <= 5; max_depth += 2){//test用
    fprintf(stderr, "************ 探索深さ = %2d ************\n", max_depth);
    bzero(HASH_TBL, sizeof(HASH_TBL));
    ret = search(&x, &y, &t, color, 1);
    fprintf(stderr, "hash_cnt = %u\n", hash_cnt);
    if( ret ) break;
  }
  if( ret == 0 ){
    fprintf(stderr, "This problem is too difficult.\n");
  }else if( ret == color ){
    place(x, y, t, bb, &bb_cnt);
    xxyyt_to_string(x - x_min_backup + 1 , y - y_min_backup + 1, t, s);
  }else if( ret == 3 - color ){
    strcpy(s, "LOST");
    fprintf(stderr, "This problem is strange ?\n");
  }

  return 0;
}






void show(){
  int x,y;
   fprintf(stderr, "  |@");
  for(x = x_min; x <= x_max; x++) fprintf(stderr, " %c", 'A' + x - x_min);
  fprintf(stderr, " |\n");
  fprintf(stderr, " 0|  ");
  for(x = x_min; x <= x_max; x++) fprintf(stderr, "  ");
  fprintf(stderr, "|\n");
  for(y = y_min; y <= y_max; y++){
    fprintf(stderr, "%2d|  ", y - y_min + 1);

    for(x = x_min; x <= x_max; x++){
      fprintf(stderr, "%s ", b_string[board[x][y]]);
    }

    fprintf(stderr, "|\n");
  }
}

int main(){
  int i, j, h ,w;
  int turn = 1;
  int ret;
  char s[16];
  char ss[16];
  int mycolor;
  char notation[300][16];
  int bb[256], bb_cnt;
  int rand = 0;
  int _time = -1;
  int n,m,l;
  char in;
  double max_search_time = 0.0;

  for(n=0; n<20; n++){
    for(m=0; m<2; m++){
      end[n][m]=0;
      start[n][m]=0;
      for(l=0; l<2; l++){
    loop_start[n][m][l]=0;
    loop_end[n][m][l]=0;
    loop_start_next[n][m][l] = 0;
    loop_end_next[n][m][l] = 0;
      }
    }
  }

  
  initForceTile();

  for( i = 0; i < BMAX; i++){
    for( j = 0; j < BMAX; j++){
      random_t[i][j][VW] = (random() << 63) | (random() << 32) | (random() << 1);
      random_t[i][j][HW] = (random() << 63) | (random() << 32) | (random() << 1);
      random_t[i][j][LRW] = (random() << 63) | (random() << 32) | (random() << 1);
      random_t[i][j][LLW] = (random() << 63) | (random() << 32) | (random() << 1);
      random_t[i][j][URW] = (random() << 63) | (random() << 32) | (random() << 1);
      random_t[i][j][ULW] = (random() << 63) | (random() << 32) | (random() << 1);
    }
  }


  //初期化重要
  for(i = 1; i <= MAX_DEPTH; i++){   //※重要※  有効な手を入れておかなくてはならない
    killer_x[i] = killer_y[i] = BMAX_2;
    killer_t[i] = VW;
  }


  if( _time == -1 ) _time = time(NULL);
  srandom(_time);
  fprintf(stderr, "*** srandom = %d\n", _time);

  rand = random() % 2;
  //  x_min = x_max = y_min = y_max = BMAX_2;
  x_min = y_min = BMAX_2 + 1;
  x_max = y_max = BMAX_2;

  fprintf(stderr, "盤面を1行で入力してください。\n");
  ret = scanf("%[^,],", s);
  j = 0;  while(s[j]==' ') j++;
  w = atoi(&s[j]);
  ret = scanf("%[^,],", s);
  j = 0;  while(s[j]==' ') j++;
  h = atoi(&s[j]);
  fprintf(stderr, "w=%d, h=%d\n", w, h);
  for(i = 0; i < w * h; i++){
    if( i == w * h -1 ) ret = scanf("%s", s);
    else ret = scanf("%[^,],", s);
    j = 0; while(s[j]==' ') j++;
    if( strncmp(&s[j], "VW", 2)==0 )       board[BMAX_2 + i % w][BMAX_2 + i / w] = VW;
    else if( strncmp(&s[j], "HW", 2)==0 )  board[BMAX_2 + i % w][BMAX_2 + i / w] = HW;
    else if( strncmp(&s[j], "ULW", 3)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = ULW;
    else if( strncmp(&s[j], "LRW", 3)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = LRW;
    else if( strncmp(&s[j], "URW", 3)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = URW;
    else if( strncmp(&s[j], "LLW", 3)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = LLW;
    else if( strncmp(&s[j], "TB", 2)==0 )  board[BMAX_2 + i % w][BMAX_2 + i / w] = VW;
    else if( strncmp(&s[j], "LR", 2)==0 )  board[BMAX_2 + i % w][BMAX_2 + i / w] = HW;
    else if( strncmp(&s[j], "TL", 2)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = ULW;
    else if( strncmp(&s[j], "BR", 2)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = LRW;
    else if( strncmp(&s[j], "TR", 2)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = URW;
    else if( strncmp(&s[j], "BL", 2)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = LLW;
    else if( strncmp(&s[j], "0", 1)==0 )   board[BMAX_2 + i % w][BMAX_2 + i / w] = 0;
    else fprintf(stderr, "Parse error\n");
    if( board[BMAX_2 + i % w][BMAX_2 + i / w] != 0 ) {
      line(BMAX_2 + i % w, BMAX_2 + i / w);
      printf("s[%d] = %s %d %d\n", i, s, BMAX_2 + i % w, BMAX_2 + i / w);}
  }

  x_min = y_min = BMAX_2;
  x_max = x_min + w - 1;
  y_max = y_min + h - 1;
  show();


  
  fprintf(stderr, "次の手番は白番ですか？ (Y/N)\n");
  
  while(1){
    in = getc(stdin);
    if( in == 'Y' || in == 'y' || in == 'N' || in == 'n' ) break;
  }
  if( in=='Y' || in=='y' ) mycolor = WHITE;
  else mycolor = RED;

  

  t1 = my_clock();
  ret = search_place(turn, s, mycolor);
  t2 = my_clock();

   printf("%s\n", s);
   strcpy(notation[turn++], s);

   if( t2 - t1 > max_search_time ) max_search_time = t2 - t1;
   fprintf(stderr, "search time = %.6f\n", t2 - t1);
   fprintf(stderr, "%s %s\n", color_s[mycolor], s);
   show();
   if( ret == 1 ){
     fprintf(stderr, "%s WINS\n", color_s[mycolor]);
     fprintf(stderr, "Max search time = %.6f\n", max_search_time);
   }
  
  /* 
  for(n=0;n<20;n++){
    if(end[n][0] != 0 ||  start[n][0] != 0 || end[n][1] != 0 || start[n][1] != 0){
      printf("\nend_red=%d  start_red=%d end_white=%d start_white=%d\n", end[n][0], start[n][0], end[n][1], start[n][1]);
      for(m=0; m<2; m++) {
	printf("loop_end[%d][x][%d] = %d loop_start[%d][x][%d] = %d end_next[%d][x][%d]=%d start_next[%d][x][%d]=%d\n",
	       n, m, loop_end[n][0][m], n, m, loop_start[n][0][m], n, m, loop_end_next[n][0][m], n, m, loop_start_next[n][0][m]);
	printf("loop_end[%d][y][%d] = %d loop_start[%d][y][%d] = %d end_next[%d][y][%d]=%d start_next[%d][y][%d]=%d\n",
	       n, m, loop_end[n][1][m], n, m, loop_start[n][1][m] , n, m, loop_end_next[n][1][m], n, m, loop_start_next[n][1][m]);
      }
    }
    }


  
    while(1){
      ret = scanf("%s", ss);
      fprintf(stderr, "%s \n", ss);
      strcpy(notation[turn++], ss);
      ret = sn_convert_place(ss);
      show();
      }
  */
    
    return 0;
}
 
