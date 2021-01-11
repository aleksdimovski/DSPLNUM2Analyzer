features int[-19,19] n;

int main() {
  //int LARGE_INT = 1000000;
  //int i,k;
  //n = [0,32767];
	
  int k = n;
  int i = 0;
  while( i < n ) {
    k--;
    i = i + 2;
  }

  int j = 0;
 
  while( j < n/2 ) {
    //assert(k > 0);
    k--;
    j++;
  }
  assert(k>=-1);
  return 0;
}
