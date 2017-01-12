#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <unistd.h>
//#include <assert.h>

#define BMAX 512
#define BMAX_2 (512/2)
#define LIMITTIME 750000   //マイクロ秒で指定
#define MAX_DEPTH 32
#define MIN(X,Y) (X)<(Y) ? (X) : (Y)
#define MAX(X,Y) (X)<(Y) ? (Y) : (X)

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

int TLIST[6] = {VW, HW, ULW, LRW, URW, LLW};

int board[BMAX][BMAX];
int lines[BMAX][BMAX][4];

typedef struct {
  int start;
  int goal;
  short length;
  short color;
} JLINEINFO;

JLINEINFO jline[1000];
int lined[1000];
int cntLines;
char ForceTile[LLW+1][LLW+1][LLW+1][LLW+1]; // 28561バイト＝28KB
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
int initial_flag=0; //初期配置と探索時の区別をするため


//標準,左右反転,上下反転,180度回転,(＼を軸にした反転)
int RR[LLW+1][8] = { {}, {}, {},
  {URW,ULW,LRW,LLW,LLW,LRW,ULW,URW}, {},
  { HW, HW, HW, HW, VW, VW, VW, VW},
  {ULW,URW,LLW,LRW,ULW,URW,LLW,LRW}, {}, {},
  {LRW,LLW,URW,ULW,LRW,LLW,URW,ULW},
  { VW, VW, VW, VW, HW, HW, HW, HW}, {},
  {LLW,LRW,ULW,URW,URW,ULW,LRW,LLW}
};

char *color_s[3]= {"", "RED", "WHITE"};
char mark[LLW+1] = {'\0','\0','\0','\\','\0','+','/','\0','\0','/','+','\0','\\'};
char *b_string[LLW+1] = {" ", "", "", "\\","","+","\x1b[31m/\x1b[0m","","","/","\x1b[31m+\x1b[0m","","\x1b[31m\\\x1b[0m"};


void show();
int tmp_search(int color, int depth);


double my_clock()
{
  struct timeval tv;
  gettimeofday(&tv, NULL);
  return tv.tv_sec + (double)tv.tv_usec*1e-6;
}

int reachcheck(int p) // p番目の線がリーチ状態になっていれば1を返す
{
  int startx, starty, startz;
  int goalx, goaly, goalz;
  int xx1, yy1, xx2, yy2; 
  startx = jline[p].start >> 12;
  starty = (jline[p].start >> 2) & 0x3ff;
  startz = jline[p].start & 3;
  goalx = jline[p].goal >> 12;
  goaly = (jline[p].goal >> 2) & 0x3ff;
  goalz = jline[p].goal & 3;

  if( startz == 0 ){
    xx1 = startx;
    yy1 = starty - 1;
  }else if( startz == 1 ){
    xx1 = startx - 1;
    yy1 = starty;
  }else if( startz == 2 ){
    xx1 = startx + 1;
    yy1 = starty;
  }else if( startz == 3 ){
    xx1 = startx;
    yy1 = starty + 1;
  }else{
    exit(1);
  }
  if( goalz == 0 ){
    xx2 = goalx;
    yy2 = goaly - 1;
  }else if( goalz == 1 ){
    xx2 = goalx - 1;
    yy2 = goaly;
  }else if( goalz == 2 ){
    xx2 = goalx + 1;
    yy2 = goaly;
  }else if( goalz == 3 ){
    xx2 = goalx;
    yy2 = goaly + 1;
  }else{
    exit(1);
  }

  if( abs(xx1-xx2) + abs(yy1-yy2) == 1 ) return 1; // 線の出口が隣同士

   // 線の出口が同じ方向(垂直or水平)で2つ隣
  if( (xx1==xx2) && (abs(yy1-yy2)==2) && (board[xx1][(yy1+yy2)>>1]==BLANK) ) return 1;
  if( (yy1==yy2) && (abs(xx1-xx2)==2) && (board[(xx1+xx2)>>1][yy1]==BLANK) ) return 1;
  

  return 0;
}

void force_place_sub(int x, int y, int a, int b, int color, int bb2[], int bb2l[], int *bb2_cnt, int bb3[], JLINEINFO bb3jline[], int *bb3_cnt, int loopflag[], int reachflag[])
{
  int p, q, s, t;
  int ax, ay, bx, by;
  int x_max2=x_max, x_min2=x_min, y_max2=y_max, y_min2=y_min;
 
 
  if( x < x_min ) x_min2 = x;
  else if( x > x_max ) x_max2 = x;
  if( y < y_min ) y_min2 = y;
  else if( y > y_max ) y_max2 = y;
  
  if( a == 0 ){
    ax = x; ay = y - 1;
    p = lines[ax][ay][3];
  }else if( a == 1 ){
    ax = x - 1; ay = y;
    p = lines[ax][ay][2];
  }else if( a == 2 ){
    ax = x + 1; ay = y;
    p = lines[ax][ay][1];
  }else if( a == 3 ){
    ax = x; ay = y + 1;
    p = lines[ax][ay][0];
  }else{
    exit(1);
  }
  if( b == 0 ){
    bx = x; by = y - 1;
    q = lines[bx][by][3];
  }else if( b == 1 ){
    bx = x - 1; by = y;
    q = lines[bx][by][2];
  }else if( b == 2 ){
    bx = x + 1; by = y;
    q = lines[bx][by][1];
  }else if( b == 3 ){
    bx = x; by = y + 1;
    q = lines[bx][by][0];
  }else{
    exit(1);
  }

  if( p == 0 && q == 0 ){
    lines[x][y][a] = lines[x][y][b] = ++cntLines;
    jline[cntLines].start = (x << 12) | (y << 2) | a;
    jline[cntLines].goal = (x << 12) | (y << 2) | b;
    jline[cntLines].color = color;
    jline[cntLines].length = 1;
    lined[cntLines] = 0; // 線を有効にする
    return;
  }else if( (p > 0) && (q > 0) ){ // 2つの線を連結する
    if( p < q ){
      s = p; t = q;
    }else if( p > q ){
      s = q; t = p;
    }else{
      loopflag[color] = 1; // ループが完成した
      return;
    }
    bb3[(*bb3_cnt)] = s;
    bb3jline[(*bb3_cnt)++] = jline[s]; //jline[s]の値を保存
    lined[t] = s;  //線tは無効にする

    int t1 = (ax << 12) | (ay << 2) | (3-a); //置いた場所の隣1
    int t2 = (bx << 12) | (by << 2) | (3-b); //置いた場所の隣2
    if( jline[s].start == t1 ){
      if( jline[t].start == t2 ){
	jline[s].start = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }else{
	jline[s].start = jline[t].start;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }
    }else if( jline[s].goal == t1 ){
      if( jline[t].start == t2 ){
	jline[s].goal = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal  >> 2) & 0x3ff][jline[s].goal  & 3] = s;
      }else{
	jline[s].goal = jline[t].start;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal  >> 2) & 0x3ff][jline[s].goal  & 3] = s;
      }
    }else if( jline[s].start == t2 ){
      if( jline[t].start == t1  ){
	jline[s].start = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }else{
	jline[s].start = jline[t].start;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }
    }else if( jline[s].goal == t2 ){
      if( jline[t].start == t1 ){
	jline[s].goal = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal >> 2) & 0x3ff][jline[s].goal & 3] = s;
      }else{
	jline[s].goal = jline[t].start;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal >> 2) & 0x3ff][jline[s].goal & 3] = s;
      }
    }else{
      exit(1);
    }
    bb2l[(*bb2_cnt)++] = t;
    jline[s].length = jline[s].length + jline[t].length  + 1;
    reachflag[color] += reachcheck(s);

  }else if( (p > 0) && (q == 0) ){

    lines[x][y][a] = lines[x][y][b] = p;  // 新しく置いた場所に線番号を登録
    bb3[(*bb3_cnt)] = p;
    bb3jline[(*bb3_cnt)++] = jline[p]; //jline[p]の値を保存

    int t1 = (ax << 12) | (ay << 2) | (3 - a);
    if( jline[p].start == t1 ){
      jline[p].start = (x << 12) | (y << 2) | b;
    }else if( jline[p].goal == t1 ){
      jline[p].goal = (x << 12) | (y << 2) | b;
    }else{
      fprintf(stderr, "bbb\n");
      fprintf(stderr, "p=%d length=%d x=%d y=%d ax=%d ay=%d a=%d (%d,%d,%d) (%d,%d,%d)\n",
	      p, jline[p].length, x, y, ax, ay, a,
	      jline[p].start >> 12, (jline[p].start >> 2) & 0x3ff, jline[p].start & 3,
	      jline[p].goal >> 12, (jline[p].goal >> 2) & 0x3ff, jline[p].goal & 3);
      show();
      exit(1);
    }
    jline[p].length++;
    reachflag[color] += reachcheck(p);
    
  }else if( (p == 0) && (q > 0) ){
    
    lines[x][y][a] = lines[x][y][b] = q; // 新しく置いた場所に線番号を登録
    bb3[(*bb3_cnt)] = q;
    bb3jline[(*bb3_cnt)++] = jline[q]; //jline[q]の値を保存

    int t2 = (bx << 12) | (by << 2) | (3 - b);
    if( jline[q].start == t2 ){
      jline[q].start = (x << 12) | (y << 2) | a;
    }else if( jline[q].goal == t2 ){
      jline[q].goal = (x << 12) | (y << 2) | a;
    }else{
      fprintf(stderr, "ccc\n");
      fprintf(stderr, "q=%d length=%d x=%d y=%d bx=%d by=%d (%d,%d,%d) (%d,%d,%d)\n",
	      q, jline[q].length, x, y, bx, by, 
	      jline[q].start >> 12, (jline[q].start >> 2) & 0x3ff, jline[q].start & 3,
	      jline[q].goal >> 12, (jline[q].goal >> 2) & 0x3ff, jline[q].goal & 3);
      show();
      exit(1);
    }
    jline[q].length++;

    reachflag[color] += reachcheck(q);
  }else{
    fprintf(stderr, "ddd\n");
    exit(1);
  }

    
}

int force_place(int x, int y, int tile, int bb[], int *bb_cnt, int bb2[], int bb2l[], int *bb2_cnt, int bb3[], JLINEINFO bb3jline[], int *bb3_cnt, int loopflag[], int reachflag[])
{
  int t;

  board[x][y] = tile;           //配置できる場所ならタイルを配置
  if( tile == VERTICAL_W ){
    force_place_sub(x, y, 0, 3, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    force_place_sub(x, y, 1, 2, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
  }else if( tile == HORIZONTAL_W ){
    force_place_sub(x, y, 1, 2, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    force_place_sub(x, y, 0, 3, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
  }else if( tile == UPPER_LEFT_W ){
    force_place_sub(x, y, 0, 1, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    force_place_sub(x, y, 2, 3, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
  }else if( tile == LOWER_RIGHT_W ){
    force_place_sub(x, y, 2, 3, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    force_place_sub(x, y, 0, 1, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
  }else if( tile == UPPER_RIGHT_W ){
    force_place_sub(x, y, 0, 2, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    force_place_sub(x, y, 1, 3, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
  }else if( tile == LOWER_LEFT_W ){
    force_place_sub(x, y, 1, 3, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    force_place_sub(x, y, 0, 2, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
  }else{
    fprintf(stderr, "eee\n");
    exit(1);
  }

  hash ^= random_t[x][y][tile];   //ハッシュ値更新
  bb[(*bb_cnt)++] = (x << 10) | y; //配置した場所を記録

  if( board[x + 1][y] == BLANK ){ // 右強制手処理
    t = ForceTile[board[x + 2][y]][board[x + 1][y - 1]][board[x][y]][board[x + 1][y + 1]];
    if( t > 0 ) t = force_place(x + 1, y, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x][y - 1] == BLANK ){ // 上強制手処理
    t = ForceTile[board[x + 1][y - 1]][board[x][y - 2]][board[x - 1][y - 1]][board[x][y]];
    if( t > 0 ) t  = force_place(x ,  y - 1, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x - 1][y] == BLANK ){ // 左強制手処理
    t = ForceTile[board[x][y]][board[x - 1][y - 1]][board[x - 2][y]][board[x - 1][y + 1]];
    if( t > 0 ) t = force_place(x - 1, y, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x][y + 1] == BLANK ){ // 下強制手処理
    t = ForceTile[board[x + 1][y + 1]][board[x][y]][board[x - 1][y + 1]][board[x][y + 2]];
    if( t > 0 ) t = force_place(x, y + 1, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  return 0;
}

int place(int x, int y, int tile, int bb[], int *bb_cnt, int bb2[], int bb2l[], int *bb2_cnt, int bb3[], JLINEINFO bb3jline[], int *bb3_cnt, int loopflag[], int reachflag[])
{
  int i;
  int hash_orig = hash;
  int cntLines_orig = cntLines;
 

  if( board[x][y] != BLANK ) return -1;
  if( PlaceableTile[board[x + 1][y]][board[x][y - 1]][board[x - 1][y]][board[x][y + 1]] & (1 << tile) ){
    *bb_cnt = 0;
    *bb2_cnt = 0;
    *bb3_cnt = 0;
    loopflag[RED] = loopflag[WHITE] = 0;
    reachflag[RED] = reachflag[WHITE] = 0;
    if( force_place(x, y, tile, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag, reachflag) == -1 ){ // 3 Same Color
      for(i = *bb2_cnt-1; i>=0;  i--){
	lines[bb2[i] >> 12][(bb2[i] >> 2) & 0x3ff][bb2[i] & 3] = bb2l[i];
	//	fprintf(stderr, "- lined[%d]=%d\n", bb2l[i], 0);
	//	assert(lined[bb2l[i]] > 0);
	lined[bb2l[i]] = 0;  //その線は有効にする
      }
      for(i = *bb3_cnt-1; i>=0;  i--) jline[bb3[i]] = bb3jline[i];
      for(i = 0; i < *bb_cnt; i++){
	int x = bb[i] >> 10;
	int y = bb[i] & 0x3ff;
        board[x][y] = 0;
	lines[x][y][0] = lines[x][y][1] = lines[x][y][2] = lines[x][y][3] = 0;
      }
      *bb_cnt = 0;
      *bb2_cnt = 0;
      *bb3_cnt = 0;
      loopflag[RED] = loopflag[WHITE] = 0;
      reachflag[RED] = reachflag[WHITE] = 0;
      hash = hash_orig;
      cntLines = cntLines_orig;
      return -1; // 3 Same Color
    }
    /*
    if(initial_flag==1){
      if(reachflag[1]==0 && reachflag[2]==0){

	if( tmp_search( 1, 1) == 1 ) reachflag[1] = 1;
	if( tmp_search( 2, 1) == 2 ) reachflag[2] = 1;

      }
      }
    */

    if( x < x_min ) x_min = x;
    else if( x > x_max ) x_max = x;
    if( y < y_min ) y_min = y;
    else if( y > y_max ) y_max = y;
    return 1;
  }
  return -1;
}

void initForceTile()
{
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
	    //  printf("%d %d %d %d  =  %d\n", t[i], t[j], t[k], t[l], ForceTile[t[i]][t[j]][t[k]][t[l]]);//確認用
	  }else if ( __builtin_popcount(wt) == 2 ){
	    ForceTile[t[i]][t[j]][t[k]][t[l]] = wt;
	    //  printf("%d %d %d %d  =  %d\n", t[i], t[j], t[k], t[l], ForceTile[t[i]][t[j]][t[k]][t[l]]);//確認用
	  }else if ( __builtin_popcount(rt) == 2 ) {
	    ForceTile[t[i]][t[j]][t[k]][t[l]] = ~rt & 0x0f;
	    //printf("%d %d %d %d  =  %d\n", t[i], t[j], t[k], t[l], ForceTile[t[i]][t[j]][t[k]][t[l]]); //確認用
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
	    // printf("%d %d %d %d %d = %d\n", t[i], t[j], t[k], t[l], t[m], ok); //確認用
	  }
	}
      }
    }
  }
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
  if( (t == VERTICAL_W) || (t == HORIZONTAL_W) ) sprintf(&s[s_cnt],"%d+", yy);
  else if( (t == UPPER_LEFT_W) || (t == LOWER_RIGHT_W) ) sprintf(&s[s_cnt],"%d/", yy);
  else sprintf(&s[s_cnt],"%d\\", yy);
}

static int killer_x[MAX_DEPTH+1], killer_y[MAX_DEPTH+1], killer_t[MAX_DEPTH+1];

int search(int *rx, int *ry, int *rt, int color, int depth);

int yrsearch(int *rx, int *ry, int *rt, int color, int depth)
{
  int i, j, x, y, t;
  int fin = 0;
  int x_min_backup = x_min;
  int x_max_backup = x_max;
  int y_min_backup = y_min;
  int y_max_backup = y_max;
  int bb[1000], bb_cnt;
  int bb2[1000], bb2l[1000], bb2_cnt;
  int bb3[1000], bb3_cnt;
  JLINEINFO bb3jline[1000];
  unsigned long long hash_backup = hash;
  int cntLines_backup = cntLines;
  int p_cnt = 0;
  int loopflag[3];
  int reachflag[3];

  //ハッシュ利用
  if( HASH_TBL[hash & HASHWIDTH] == (hash | (color - 1)) ){
    return WINLOSS[hash & HASHWIDTH]; // ハッシュに登録済
  }

  //キラームーブチェック
  x = killer_x[depth];
  y = killer_y[depth];
  t = killer_t[depth];

  if( board[x][y] == BLANK ){
    if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
      if( place(x, y, t, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == 1 ){
	if( loopflag[color]==1 ){
	  fin = 1;
	}else{
	  if( depth < max_depth ){
	    if( loopflag[3-color]==0 ){ // 相手のループはできていない
	      int ret;
	      int _rx, _ry, _rt;
	      ret = search(&_rx, &_ry, &_rt, 3 - color, depth + 1);
	      if( ret == color ){
		fin = 1; // 自分が勝つ
	      }
	    }
	  }
	}
	for(j = bb2_cnt-1; j>=0;  j--){
	  lines[bb2[j] >> 12][(bb2[j] >> 2) & 0x3ff][bb2[j] & 3] = bb2l[j];
	  lined[bb2l[j]] = 0;  //その線は有効にする
	}
	for(j = bb3_cnt-1; j>=0;  j--) jline[bb3[j]] = bb3jline[j];
	for(j = 0; j < bb_cnt; j++){
	  int x = bb[j] >> 10;
	  int y = bb[j] & 0x3ff;
	  board[x][y] = 0;
	  lines[x][y][0] = lines[x][y][1] = lines[x][y][2] = lines[x][y][3] = 0;
	}
	hash = hash_backup;
	cntLines = cntLines_backup;
	x_min = x_min_backup;
	x_max = x_max_backup;
	y_min = y_min_backup;
	y_max = y_max_backup;
	if( fin == 1 ) {
	  // HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
	  // WINLOSS[hash & HASHWIDTH] = color; //ハッシュ登録
	  // hash_cnt++;
	  return color;
	}
      }
    }
  }

  for(y = y_min - 1; y <= y_max + 1; y++){
    for(x = x_min - 1; x <= x_max + 1; x++){
      if( board[x][y] ) continue;
      if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
	if( depth==2 ){
	  if( x == x_min - 1 ) fprintf(stderr, " d=%d %d %d @%d", depth, x, y, y - y_min + 1);
	  else fprintf(stderr, " d=%d %d %d %c%d", depth, x, y, x - x_min + 'A', y - y_min + 1);
	}
	for(i = 0; i < 6; i++){
	  t = TLIST[i];
	  if( place(x, y, t, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == 1 ){
	    if( loopflag[color]==1 ){ // 自分のLoopができた
	      killer_x[depth] = x; killer_y[depth] = y;  killer_t[depth] = t;
	      fin = 1;
	    }else{ // 相手のLoopを確認する
	      if( loopflag[3 - color]==0 ){ // 相手のループはできていない
		if( depth < max_depth ){
		  int ret;
		  int _rx, _ry, _rt;
		  ret = search(&_rx, &_ry, &_rt, 3 - color, depth + 1);
		  if( ret == color ){
		    if( depth==2 ) fprintf(stderr, " %c(K) ", mark[t]);
		    killer_x[depth] = x; killer_y[depth] = y;  killer_t[depth] = t;
		    fin = 1; // 自分が勝つ
		  }else if( ret == 3 - color ){
		    if( depth==2 ) fprintf(stderr, " %c(M) ", mark[t]);
		    // 何もしない
		  }else{ //勝敗付かない
		    if( depth==2 ) fprintf(stderr, " %c ", mark[t]);
		    p_cnt++;
		  }
		}else{ // 末端(depth == max_depth)
		    if( depth==2 ) fprintf(stderr, " %c ", mark[t]);
		  p_cnt++;
		}
	      }else{
		if( depth==2 ) fprintf(stderr, " %c(M) ", mark[t]);
	      }
	    }
	    for(j = bb2_cnt-1; j>=0;  j--){
	      lines[bb2[j] >> 12][(bb2[j] >> 2) & 0x3ff][bb2[j] & 3] = bb2l[j];
	      if( lined[bb2l[j]] == 0 ){
		show();
		fprintf(stderr, "*** %d %d\n", bb2_cnt, j);
	      }
	      lined[bb2l[j]] = 0;  //その線は有効にする
	    }
	    for(j = bb3_cnt-1; j>=0;  j--) jline[bb3[j]] = bb3jline[j];
	    for(j = 0; j < bb_cnt; j++){
	      int x = bb[j] >> 10;
	      int y = bb[j] & 0x3ff;
	      board[x][y] = 0;
	      lines[x][y][0] = lines[x][y][1] = lines[x][y][2] = lines[x][y][3] = 0;
	    }
	    hash = hash_backup;
	    cntLines = cntLines_backup;
	    x_min = x_min_backup;  x_max = x_max_backup;
	    y_min = y_min_backup;  y_max = y_max_backup;
	  
	    if( fin == 1 ){
	      //HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
	      //WINLOSS[hash & HASHWIDTH] = color; //ハッシュ登録
	      //hash_cnt++;
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
  if( p_cnt == 0 ) { //防ぐ手がないので自分の負け
    HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
    WINLOSS[hash & HASHWIDTH] = 3 - color; //ハッシュ登録
    hash_cnt++;
    return 3 - color; 
  }
  return 0;
}
int search(int *rx, int *ry, int *rt, int color, int depth)
{
  int i, j, x, y, t;
  int fin = 0;
  int x_min_backup = x_min;
  int x_max_backup = x_max;
  int y_min_backup = y_min;
  int y_max_backup = y_max;
  int bb[1000], bb_cnt;
  int bb2[1000], bb2l[1000], bb2_cnt;
  int bb3[1000], bb3_cnt;
  JLINEINFO bb3jline[1000];
  unsigned long long hash_backup = hash;
  int cntLines_backup = cntLines;
  int px[1000], py[1000], pt[1000]; // depth=1 のときしか使わない
  int p_cnt = 0;
  int myriichi, yrriichi;
  int loopflag[3];
  int reachflag[3];

  //ハッシュ利用
  if( depth > 1 ){
    if( HASH_TBL[hash & HASHWIDTH] == (hash | (color - 1)) ){
      return WINLOSS[hash & HASHWIDTH]; // ハッシュに登録済
    }
  }

  //キラームーブチェック
  if( depth > 1){
    x = killer_x[depth];
    y = killer_y[depth];
    t = killer_t[depth];

    if( board[x][y] == BLANK ){
      if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
	if( place(x, y, t, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == 1 ){
	  if( loopflag[color] == 1 ){ 
	    fin = 1;
	  }else{
	    if( depth < max_depth ){
	      if( loopflag[3-color] == 0 ){ // 相手のループはできていない
		int ret;
		int _rx, _ry, _rt;
		ret = yrsearch(&_rx, &_ry, &_rt, 3 - color, depth + 1);
		if( ret == color ){
		  fin = 1; // 自分が勝つ
		}
	      }
	    }
	  }
	  for(j = bb2_cnt-1; j>=0;  j--){
	    lines[bb2[j] >> 12][(bb2[j] >> 2) & 0x3ff][bb2[j] & 3] = bb2l[j];
	    lined[bb2l[j]] = 0;  //その線は有効にする
	  }
	  for(j = bb3_cnt-1; j>=0;  j--) jline[bb3[j]] = bb3jline[j];
	  for(j = 0; j < bb_cnt; j++){
	    int x = bb[j] >> 10;
	    int y = bb[j] & 0x3ff;
	    board[x][y] = 0;
	    lines[x][y][0] = lines[x][y][1] = lines[x][y][2] = lines[x][y][3] = 0;
	  }
	  hash = hash_backup;
	  cntLines = cntLines_backup;
	  x_min = x_min_backup;
	  x_max = x_max_backup;
	  y_min = y_min_backup;
	  y_max = y_max_backup;
	  if( fin == 1 ) {
	    //	    HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
	    //	    WINLOSS[hash & HASHWIDTH] = color; //ハッシュ登録
	    //	    hash_cnt++;
	    return color;
	  }
	}
      }
    }
  }

  for(y = y_min - 1; y <= y_max + 1; y++){
    for(x = x_min - 1; x <= x_max + 1; x++){
      if( board[x][y] ) continue;
      if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
	if( depth==1 ){
	  if( x == x_min - 1 ) fprintf(stderr, "d=%d %d %d @%d", depth, x, y, y - y_min + 1);
	  else fprintf(stderr, "d=%d %d %d %c%d", depth, x, y, x - x_min + 'A', y - y_min + 1);
	}
	for(i = 0; i < 6; i++){
	  t = TLIST[i];
	  if( place(x, y, t, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == 1 ){
	    myriichi = reachflag[color];
	    yrriichi = reachflag[3-color];
	    if( loopflag[color] == 1 ){ 
	      if( depth==1 ) fprintf(stderr, " %c %s-LoopOrLine ", mark[t], color_s[color]);
	      killer_x[depth] = x; killer_y[depth] = y;  killer_t[depth] = t;
	      fin = 1;
	    }else{ // 相手のLoopを確認する
	      if(  myriichi==0 && yrriichi == 0 && depth == 1){
		  if(  tmp_search( color, 1) == color) myriichi=1;
	      }
	      if( loopflag[3-color]==0 && myriichi==0 && yrriichi == 0){ // 相手のループはできていないしリートもしていないなら読まない
		 
	      }else if( (loopflag[3-color]==0) && (myriichi > 0)){ // 相手のループはできていない
		if( depth < max_depth ){
		  int ret;
		  int _rx, _ry, _rt;
		  ret = yrsearch(&_rx, &_ry, &_rt, 3 - color, depth + 1);
		  if( ret == color ){
		    if( depth==1 ){
		      fprintf(stderr, " %c(**KACHI**)", mark[t]);
		    }
		    killer_x[depth] = x; killer_y[depth] = y;  killer_t[depth] = t;
		    fin = 1; // 自分が勝つ
		  }else if( ret == 3 - color ){ // 相手が勝つ
		    // デバッグ用コード(すでに登録されていることを確認)
		    /*
		    if( (HASH_TBL[hash & HASHWIDTH] != (hash | ( 2 - color)) ) || (WINLOSS[hash & HASHWIDTH] != 3-color) ){
		      fprintf(stderr, " Error\n");
		      exit(0);
		    }
		    */
		    if( depth==1 ) fprintf(stderr, " %c(L)", mark[t]);
		  }else{ //勝敗付かない
		    if( depth==1 ) {
		      if( myriichi > 0 ) fprintf(stderr, " %c(R)", mark[t]);
		      else fprintf(stderr, " %c", mark[t]);
		      if( myriichi > 0 ){
			px[p_cnt] = x; py[p_cnt] = y; pt[p_cnt] = t;
		      }
		    }
		    p_cnt++;
		  }
		}else{ // 末端(depth == max_depth)
		  if( depth == 1 ){ // MAX_DEPTH と depth の両方とも 1 のとき
		    if( myriichi > 0 ) fprintf(stderr, " %c(R)", mark[t]);
		    else fprintf(stderr, " %c", mark[t]);
		    if( myriichi > 0 ){
		      px[p_cnt] = x; py[p_cnt] = y; pt[p_cnt] = t;
		    }
		  }
		  p_cnt++;
		}
	      }else{ //相手のループができて負け
		if( depth==1 ) fprintf(stderr, " %c(L)", mark[t]);
	      }
	    }
	    for(j = bb2_cnt-1; j>=0;  j--){
	      lines[bb2[j] >> 12][(bb2[j] >> 2) & 0x3ff][bb2[j] & 3] = bb2l[j];
	      lined[bb2l[j]] = 0;  //その線は有効にする
	    }
	    for(j = bb3_cnt-1; j>=0;  j--) jline[bb3[j]] = bb3jline[j];
	    for(j = 0; j < bb_cnt; j++){
	      int x = bb[j] >> 10;
	      int y = bb[j] & 0x3ff;
	      board[x][y] = 0;
	      lines[x][y][0] = lines[x][y][1] = lines[x][y][2] = lines[x][y][3] = 0;
	    }
	    hash = hash_backup;
	    cntLines = cntLines_backup;
	    x_min = x_min_backup;  x_max = x_max_backup;
	    y_min = y_min_backup;  y_max = y_max_backup;
	  
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
  if( p_cnt == 0 ) { //防ぐ手がないので自分の負け
    //    HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
    //    WINLOSS[hash & HASHWIDTH] = 3 - color; //ハッシュ登録
    //    hash_cnt++;
    return 3 - color; 
  }
  if( depth == 1 ){
    int r = random() % p_cnt;
    *rx = px[r];
    *ry = py[r];
    *rt = pt[r];
  }
  return 0;
}

int search_place(int turn, char s[], int color)
{
  int x = 0, y = 0, t = 0;
  int x_min_backup = x_min;
  int y_min_backup = y_min;
  int ret;
  int bb[256], bb_cnt;
  int bb2[256], bb2l[256], bb2_cnt;
  int bb3[256], bb3_cnt;
  JLINEINFO bb3jline[256];
  int loopflag[3];
  int reachflag[3];

  for(max_depth = 1 ; max_depth <= MAX_DEPTH; max_depth += 2 ){
    fprintf(stderr, "************ 探索深さ = %2d ************\n", max_depth);
    bzero(HASH_TBL, sizeof(HASH_TBL));
    ret = search(&x, &y, &t, color, 1);
    fprintf(stderr, "hash_cnt = %u\n", hash_cnt);
    if( ret ) break;
  }
  if( ret == 0 ){
    fprintf(stderr, "This problem is too difficult.\n");
  }else if( ret == color ){
    place(x, y, t, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    xxyyt_to_string(x - x_min_backup + 1 , y - y_min_backup + 1, t, s);
  }else if( ret == 3 - color ){
    strcpy(s, "LOST");
    fprintf(stderr, "This problem is strange ?\n");
  }
  return 0;
}

int sn_convert_place(char s[])
 {
  int i;
  int xx = 0;
  int yy = 0;
  char ss = '\0';
  int bb[256], bb_cnt;
  int bb2[256], bb2l[256], bb2_cnt;
  int bb3[256], bb3_cnt;
  JLINEINFO bb3jline[256];
  int loopflag[3];
  int reachflag[3];

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
    if (place(x, y, UPPER_RIGHT_W, bb, &bb_cnt, bb2, bb2l,&bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == -1){
      if (place(x, y, LOWER_LEFT_W, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == -1){
        fprintf(stderr, "Can not place\n");
        //exit(0);
      }
    }
  }else if (ss == '/'){
    if (place(x, y, UPPER_LEFT_W, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == -1){
      if (place(x, y, LOWER_RIGHT_W, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == -1) {
        fprintf(stderr, "Can not place\n");
        //exit(0);
      }
    }
  }else if (ss == '+'){
    if (place(x, y, VERTICAL_W, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == -1){
      if (place(x, y, HORIZONTAL_W, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag) == -1) {
        fprintf(stderr, "Can not place\n");
        //exit(0);
      }
    }
  }else{
    fprintf(stderr, "Can not place\n");
  }
  if( loopflag[RED] == 1 ){
    return RED;
  }

  if( loopflag[WHITE] == 1 ){
    return WHITE;
  }
  return 0;
}

void line_show()
{
  int i;
  for(i = 1; i <= cntLines; i++){
    fprintf(stderr, "%d start=(%d,%d,%d) goal=(%d,%d,%d) len=%d col=%d dis=%d\n",
	    i, jline[i].start >> 12, (jline[i].start >> 2) & 0x3ff,jline[i].start & 3,
	    jline[i].goal >> 12, (jline[i].goal >> 2) & 0x3ff, jline[i].goal & 3,
	    jline[i].length, jline[i].color, lined[i]);
  }
}

void show()
{
  int x, y;
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
  line_show();
}

int main(int argc, char* argv[])
{
  int i, j, w, h;
  int turn = 1;
  int ret;
  char s[16];
  int mycolor;
  char notation[300][16];
  double max_search_time = 0.0;
  char in;
  int bb[100], bb_cnt;
  int bb2[100], bb2l[100], bb2_cnt;
  int bb3[100], bb3_cnt;
  JLINEINFO bb3jline[100];
  int loopflag[3];
  int reachflag[3];

  FILE *fp, *fp2;
  int prob_num;


  if (argc == 2)prob_num = atoi(argv[1]);
  else {
    printf("コマンドライン引数で問題番号を与えてください\n");
    exit(0);
  }

  if ((fp = fopen("Prob_loop_solved300.txt", "r")) == NULL) {
    printf("ファイルが開けません\n");
    exit(0);
  }
  while (fscanf(fp, "%[^,],", s) != EOF) {
    j = 0; while (s[j] == ' ' || s[j] == '\n' || s[j] == '\r')j++;
    if (s[j] == 'P') {
      if (atoi(&s[j+1]) == prob_num) {
        break;
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

  //  x_min = x_max = y_min = y_max = BMAX_2;
  x_min = y_min = BMAX_2 + 1;
  x_max = y_max = BMAX_2;

  fprintf(stderr, "盤面を1行で入力してください。\n");
  ret = fscanf(fp, "%[^,],", s);
  j = 0;  while(s[j]==' ') j++;
  w = atoi(&s[j]);
  ret = fscanf(fp, "%[^,],", s);
  j = 0;  while(s[j]==' ') j++;
  h = atoi(&s[j]);
  fprintf(stderr, "w=%d, h=%d\n", w, h);

  for(i = 0; i < w * h; i++){
    if( i == w * h -1 ) ret = fscanf(fp, "%[^,],", s);
    else ret = fscanf(fp, "%[^,],", s);
    j = 0; while(s[j]==' ') j++;
    int x = BMAX_2 + i % w;
    int y = BMAX_2 + i / w;
    if( strncmp(&s[j], "VW", 2)==0 ) place(x, y, VW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "HW", 2)==0 )  place(x, y, HW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "ULW", 3)==0 ) place(x, y, ULW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "LRW", 3)==0 ) place(x, y, LRW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "URW", 3)==0 ) place(x, y, URW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "LLW", 3)==0 ) place(x, y, LLW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "TB", 2)==0 )  place(x, y, VW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "LR", 2)==0 )  place(x, y, HW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "TL", 2)==0 ) place(x, y, ULW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "BR", 2)==0 ) place(x, y, LRW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "TR", 2)==0 ) place(x, y, URW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "BL", 2)==0 ) place(x, y, LLW, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag, reachflag);
    else if( strncmp(&s[j], "0", 1)==0 ) board[BMAX_2 + i % w][BMAX_2 + i / w] = 0;
    else fprintf(stderr, "Parse error\n");
    show();
  }

  x_min = y_min = BMAX_2;
  x_max = x_min + w - 1;
  y_max = y_min + h - 1;
  show();

  // fprintf(stderr, "次の手番は白番ですか？ (Y/N)\n");
  while(1){
    //in = getc(stdin);
    //    if( in == 'Y' || in == 'y' || in == 'N' || in == 'n' ) break;
    ret = fscanf(fp, "%[^,],", s);
    if (s[0] == 'W' || s[0] == 'B') break;
    if (s[1] == 'W' || s[1] == 'B') break;
  }
  //  if( in=='Y' || in=='y' ) mycolor = WHITE;
  //  else mycolor = RED;
  if (s[0] == 'W') mycolor = WHITE;
  else if (s[1] == 'W') mycolor = WHITE;
  else mycolor = RED;

  initial_flag=1;
 
  fclose(fp);
 
  t1 = my_clock();
  ret = search_place(turn, s, mycolor);
  t2 = my_clock();
  strcpy(notation[turn++], s);

  if ((fp2 = fopen("result300.csv", "a")) == NULL) {
    printf("file open error!!\n");
    exit(EXIT_FAILURE);/* (3)エラーの場合は通常、異常終了する */
  }


  fprintf( fp2, "%d,%s,%.6f\n",prob_num, s,t2-t1 );
  fclose( fp2 );



  if( t2 - t1 > max_search_time ) max_search_time = t2 - t1;
  fprintf(stderr, "search time = %.6f\n", t2 - t1);
  fprintf(stderr, "%s %s\n", color_s[mycolor], s);
  show();
  if( ret ){
    fprintf(stderr, "%s WINS\n", color_s[mycolor]);
    fprintf(stderr, "Max search time = %.6f\n", max_search_time);
    return 0;
  }
  //// とりあえず一旦終了する。
 

  return 0;
}


void loopcheck(int x, int y, int a, int b, int color, int bb2[], int bb2l[], int *bb2_cnt, int bb3[], JLINEINFO bb3jline[], int *bb3_cnt, int loopflag[]){
  int p, q, s, t;
  int ax, ay, bx, by;

  
  if( a == 0 ){
    ax = x; ay = y - 1;
    p = lines[ax][ay][3];
  }else if( a == 1 ){
    ax = x - 1; ay = y;
    p = lines[ax][ay][2];
  }else if( a == 2 ){
    ax = x + 1; ay = y;
    p = lines[ax][ay][1];
  }else if( a == 3 ){
    ax = x; ay = y + 1;
    p = lines[ax][ay][0];
  }else{
    exit(1);
  }
  if( b == 0 ){
    bx = x; by = y - 1;
    q = lines[bx][by][3];
  }else if( b == 1 ){
    bx = x - 1; by = y;
    q = lines[bx][by][2];
   }else if( b == 2 ){
    bx = x + 1; by = y;
    q = lines[bx][by][1];
  }else if( b == 3 ){
    bx = x; by = y + 1;
    q = lines[bx][by][0];
  }else{
    exit(1);
  }
  


  if( p == 0 && q == 0 ){
    lines[x][y][a] = lines[x][y][b] = ++cntLines;
    jline[cntLines].start = (x << 12) | (y << 2) | a;
    jline[cntLines].goal = (x << 12) | (y << 2) | b;
    jline[cntLines].color = color;
    jline[cntLines].length = 1;
    lined[cntLines] = 0; // 線を有効にする
  }else if( (p > 0) && (q > 0) ){ // 2つの線を連結する
    if( p < q ){
      s = p; t = q;
    }else if( p > q ){
      s = q; t = p;
    }else{
      loopflag[color] = 1;
       return;
    }
         
    bb3[(*bb3_cnt)] = s;
    bb3jline[(*bb3_cnt)++] = jline[s]; //jline[s]の値を保存
    lined[t] = s;  //線tは無効にする
    
    int t1 = (ax << 12) | (ay << 2) | (3-a); //置いた場所の隣1
    int t2 = (bx << 12) | (by << 2) | (3-b); //置いた場所の隣2
    if( jline[s].start == t1 ){
      if( jline[t].start == t2 ){
	jline[s].start = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }else{
	jline[s].start = jline[t].start;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }
    }else if( jline[s].goal == t1 ){
      if( jline[t].start == t2 ){
	jline[s].goal = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal  >> 2) & 0x3ff][jline[s].goal  & 3] = s;
      }else{
	jline[s].goal = jline[t].start;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal  >> 2) & 0x3ff][jline[s].goal  & 3] = s;
      }
    }else if( jline[s].start == t2 ){
      if( jline[t].start == t1  ){
	jline[s].start = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }else{
	jline[s].start = jline[t].start;
	bb2[*bb2_cnt] = jline[s].start; // 状態を保存
	lines[jline[s].start >> 12][(jline[s].start >> 2) & 0x3ff][jline[s].start & 3] = s;
      }
    }else if( jline[s].goal == t2 ){
      if( jline[t].start == t1 ){
	jline[s].goal = jline[t].goal;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal >> 2) & 0x3ff][jline[s].goal & 3] = s;
      }else{
	jline[s].goal = jline[t].start;
	bb2[*bb2_cnt] = jline[s].goal; // 状態を保存
	lines[jline[s].goal  >> 12][(jline[s].goal >> 2) & 0x3ff][jline[s].goal & 3] = s;
      }
    }else{
      exit(1);
    }
    bb2l[(*bb2_cnt)++] = t;
    jline[s].length = jline[s].length + jline[t].length  + 1;
     
  }else if( (p > 0) && (q == 0) ){
    
    lines[x][y][a] = lines[x][y][b] = p;  // 新しく置いた場所に線番号を登録
    bb3[(*bb3_cnt)] = p;
    bb3jline[(*bb3_cnt)++] = jline[p]; //jline[p]の値を保存
    
    int t1 = (ax << 12) | (ay << 2) | (3 - a);
    if( jline[p].start == t1 ){
      jline[p].start = (x << 12) | (y << 2) | b;
    }else if( jline[p].goal == t1 ){
      jline[p].goal = (x << 12) | (y << 2) | b;
    }else{
      fprintf(stderr, "bbb\n");
      fprintf(stderr, "p=%d length=%d x=%d y=%d ax=%d ay=%d a=%d (%d,%d,%d) (%d,%d,%d)\n",
	      p, jline[p].length, x, y, ax, ay, a,
	      jline[p].start >> 12, (jline[p].start >> 2) & 0x3ff, jline[p].start & 3,
	      jline[p].goal >> 12, (jline[p].goal >> 2) & 0x3ff, jline[p].goal & 3);
      show();
      exit(1);
    }
    jline[p].length++;
    
  }else if( (p == 0) && (q > 0) ){
    
    lines[x][y][a] = lines[x][y][b] = q; // 新しく置いた場所に線番号を登録
    bb3[(*bb3_cnt)] = q;
    bb3jline[(*bb3_cnt)++] = jline[q]; //jline[q]の値を保存
    
    int t2 = (bx << 12) | (by << 2) | (3 - b);
    if( jline[q].start == t2 ){
      jline[q].start = (x << 12) | (y << 2) | a;
    }else if( jline[q].goal == t2 ){
      jline[q].goal = (x << 12) | (y << 2) | a;
    }else{
      fprintf(stderr, "ccc\n");
      fprintf(stderr, "q=%d length=%d x=%d y=%d bx=%d by=%d (%d,%d,%d) (%d,%d,%d)\n",
	      q, jline[q].length, x, y, bx, by, 
	      jline[q].start >> 12, (jline[q].start >> 2) & 0x3ff, jline[q].start & 3,
	      jline[q].goal >> 12, (jline[q].goal >> 2) & 0x3ff, jline[q].goal & 3);
      show();
      exit(1);
    }
    jline[q].length++;
  }else{
    fprintf(stderr, "ddd\n");
    exit(1);
  }
  /*
  int i;
  if(x==261 && y==258 && color == WHITE){
    fprintf(stderr, "a=%d b=%d", a,b);
    for(i = 1; i <= cntLines; i++){
      if(jline[i].color==2 && lined[i] ==0 )
        fprintf(stderr, "%d start=(%d,%d,%d) goal=(%d,%d,%d) len=%d col=%d dis=%d\n",
                i, jline[i].start >> 12, (jline[i].start >> 2) & 0x3ff,jline[i].start & 3,
                jline[i].goal >> 12, (jline[i].goal >> 2) & 0x3ff, jline[i].goal & 3,
                jline[i].length, jline[i].color, lined[i]);
    }
  }   
  */
  return;
}

int tmp_force_place(int x, int y, int tile, int bb[], int *bb_cnt, int bb2[], int bb2l[], int *bb2_cnt, int bb3[], JLINEINFO bb3jline[], int *bb3_cnt, int loopflag[]){

  int t;


  board[x][y] = tile;           //配置できる場所ならタイルを配置
  if( tile == VERTICAL_W ){
    loopcheck(x, y, 0, 3, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    loopcheck(x, y, 1, 2, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
  }else if( tile == HORIZONTAL_W ){
    loopcheck(x, y, 1, 2, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    loopcheck(x, y, 0, 3, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
  }else if( tile == UPPER_LEFT_W ){
    loopcheck(x, y, 0, 1, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    loopcheck(x, y, 2, 3, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
  }else if( tile == LOWER_RIGHT_W ){
    loopcheck(x, y, 2, 3, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    loopcheck(x, y, 0, 1, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
  }else if( tile == UPPER_RIGHT_W ){
    loopcheck(x, y, 0, 2, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    loopcheck(x, y, 1, 3, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
  }else if( tile == LOWER_LEFT_W ){
    loopcheck(x, y, 1, 3, WHITE, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    loopcheck(x, y, 0, 2, RED, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
  }else{
    fprintf(stderr, "eee\n");
    exit(1);
  }

  hash ^= random_t[x][y][tile];   //ハッシュ値更新
  bb[(*bb_cnt)++] = (x << 10) | y; //配置した場所を記録

  if( board[x + 1][y] == BLANK ){ // 右強制手処理
    t = ForceTile[board[x + 2][y]][board[x + 1][y - 1]][board[x][y]][board[x + 1][y + 1]];
    if( t > 0 ) t = tmp_force_place(x + 1, y, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x][y - 1] == BLANK ){ // 上強制手処理
    t = ForceTile[board[x + 1][y - 1]][board[x][y - 2]][board[x - 1][y - 1]][board[x][y]];
    if( t > 0 ) t  = tmp_force_place(x ,  y - 1, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x - 1][y] == BLANK ){ // 左強制手処理
    t = ForceTile[board[x][y]][board[x - 1][y - 1]][board[x - 2][y]][board[x - 1][y + 1]];
    if( t > 0 ) t = tmp_force_place(x - 1, y, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  if( board[x][y + 1] == BLANK ){ // 下強制手処理
    t = ForceTile[board[x + 1][y + 1]][board[x][y]][board[x - 1][y + 1]][board[x][y + 2]];
    if( t > 0 ) t = tmp_force_place(x, y + 1, t, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag);
    if( t == -1 ) return -1; // 3 Same Color
  }
  return 0;
}

int tmp_place(int x, int y, int tile, int bb[], int *bb_cnt, int bb2[], int bb2l[], int *bb2_cnt, int bb3[], JLINEINFO bb3jline[], int *bb3_cnt, int loopflag[]){
  int i;
  int hash_orig = hash;
  int cntLines_orig = cntLines;
  
  if( board[x][y] != BLANK ) return -1;
  if( PlaceableTile[board[x + 1][y]][board[x][y - 1]][board[x - 1][y]][board[x][y + 1]] & (1 << tile) ){
    *bb_cnt = 0;
    *bb2_cnt = 0;
    *bb3_cnt = 0;
    loopflag[RED] = loopflag[WHITE] = 0;
    if( tmp_force_place(x, y, tile, bb, bb_cnt, bb2, bb2l, bb2_cnt, bb3, bb3jline, bb3_cnt, loopflag) == -1 ){ // 3 Same Color
      for(i = *bb2_cnt-1; i>=0;  i--){
	lines[bb2[i] >> 12][(bb2[i] >> 2) & 0x3ff][bb2[i] & 3] = bb2l[i];
	//fprintf(stderr, "- lined[%d]=%d\n", bb2l[i], 0);
	//assert(lined[bb2l[i]] > 0);
	lined[bb2l[i]] = 0;  //その線は有効にする
      }
      for(i = *bb3_cnt-1; i>=0;  i--) jline[bb3[i]] = bb3jline[i];
      for(i = 0; i < *bb_cnt; i++){
	int x = bb[i] >> 10;
	int y = bb[i] & 0x3ff;
	board[x][y] = 0;
	lines[x][y][0] = lines[x][y][1] = lines[x][y][2] = lines[x][y][3] = 0;
      }
      *bb_cnt = 0;
      *bb2_cnt = 0;
      *bb3_cnt = 0;
      loopflag[RED] = loopflag[WHITE] = 0;
      hash = hash_orig;
      cntLines = cntLines_orig;
      return -1; // 3 Same Color
    }
    if( x < x_min ) x_min = x;
    else if( x > x_max ) x_max = x;
    if( y < y_min ) y_min = y;
    else if( y > y_max ) y_max = y;
    return 1;
  }
  return -1;
}



int tmp_search(int color, int depth){
  int i, j, x, y, t;
  int fin = 0;
  int x_min_backup = x_min;
  int x_max_backup = x_max;
  int y_min_backup = y_min;
  int y_max_backup = y_max;
  int bb[1000], bb_cnt;
  int bb2[1000], bb2l[1000], bb2_cnt;
  int bb3[1000], bb3_cnt;
  JLINEINFO bb3jline[1000];
  unsigned long long hash_backup = hash;
  int cntLines_backup = cntLines;
  int px[1000], py[1000], pt[1000]; // depth=1 のときしか使わない
  int p_cnt = 0;
  int loopflag[3];

  // x=259;y=257;t=LLW;
  
  for(y = y_min - 1; y <= y_max + 1; y++){
    for(x = x_min - 1; x <= x_max + 1; x++){
      if( board[x][y] ) continue;
      if( board[x-1][y] | board[x+1][y] | board[x][y-1] | board[x][y+1] ){
	for(i = 0; i < 6; i++){
          t = TLIST[i];
          if( tmp_place(x, y, t, bb, &bb_cnt, bb2, bb2l, &bb2_cnt, bb3, bb3jline, &bb3_cnt, loopflag) == 1 ){
	    
	    
	    for(j = bb2_cnt-1; j>=0;  j--){
	      lines[bb2[j] >> 12][(bb2[j] >> 2) & 0x3ff][bb2[j] & 3] = bb2l[j];
	      lined[bb2l[j]] = 0;  //その線は有効にする
	    }
	    for(j = bb3_cnt-1; j>=0;  j--) jline[bb3[j]] = bb3jline[j];
	    for(j = 0; j < bb_cnt; j++){
	      int x = bb[j] >> 10;
	      int y = bb[j] & 0x3ff;
	      board[x][y] = 0;
	      lines[x][y][0] = lines[x][y][1] = lines[x][y][2] = lines[x][y][3] = 0;
	    }
	    
            hash = hash_backup;
	    cntLines = cntLines_backup;
            x_min = x_min_backup;  x_max = x_max_backup;
            y_min = y_min_backup;  y_max = y_max_backup;
	    
            if( loopflag[color] == 1 ){

              HASH_TBL[hash & HASHWIDTH] = hash | (color - 1);
              WINLOSS[hash & HASHWIDTH] = color; //ハッシュ登録
              hash_cnt++;
              return color;
            }
	  }
	}
      }
    }
  }
  
  return 0;

}

