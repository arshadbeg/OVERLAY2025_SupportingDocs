/* takes as input an integer and returns 
   its (integer) square root */
int root(int N){
  int R = 0;
  while(((R+1)*(R+1)) <= N) {
    R = R + 1;
  }
  return R;
}
