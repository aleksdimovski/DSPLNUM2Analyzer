features int[-9,9] n0;
features int[-9,9] n1;
//features int[0,4] A3;

int main() {

//  int n0, n1;
  int i0 = 0;
  int k = 0;

//  n0 = [-9,9]; //__VERIFIER_nondet_int();
//  n1 = [-9,9]; //__VERIFIER_nondet_int();
	
  while( i0 < n0 ) {
    i0++;
    k++;
  }

  int i1 = 0;
  while( i1 < n1 ) {
    i1++;
    k++;
  }

  int j1 = 0;
  while( j1 < n0 + n1 ) {
      //assert(k > 0);
      j1++;
      k--;
  }
  assert(k==0); 
}
