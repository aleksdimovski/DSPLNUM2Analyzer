features int[0,99] A;

int main() {
   A=[10,15];
  int x=10, y=0;
  if (A>=12) y=1; else y=-1;
  while (x>0) {
	  A = A+y;
	  x = x-1;
  }
  assert (y>=0);
  return 0;
}