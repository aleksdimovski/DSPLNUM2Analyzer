//features int[0,5] A1;

int main() {
  //int LARGE_INT = 1000000;
  int n,i,k;
  n = [-19,19];
	
  k = n;
  i = 0;
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
