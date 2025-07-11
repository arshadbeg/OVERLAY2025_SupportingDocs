/* swaps two pointed values */
void swap(int *a, int *b){
  int tmp = *a ; *a = *b ; *b = tmp ;
}

int main(){
  int x = 2;
  int y = 4;
  swap(&x, &y);
}
