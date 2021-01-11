//features int[0,109] A;


int main() {
  int y=5, x=10; 
  int A=[0,9];
  while (x>=0) {
	  if (A<=5) {y=y+A;} else {y=y-A;}
	  x = x-1;
  }
  A=A+1;
  if (A<=6) assert (y>=5); else assert(y<=-61); 
  return 0;
}