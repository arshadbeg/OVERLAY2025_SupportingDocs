int max(int a, int b){
  return (a >= b) ? a : b ;
}

extern int x ;

int main(){
  x = 3;
  int r = max(4, 2);
}
