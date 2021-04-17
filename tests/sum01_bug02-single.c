//features int[0,4] A1;
//features int[0,4] A2;


int main() { 
  int a = 2;
  int i, j=10, sn=0;
  int n=[0,19]; 
	
  for(i=1; i<=n; i++) {
    if (j>n) sn = sn + a;
    j--;
  }
  assert(sn==n*a);
}
