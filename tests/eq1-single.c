//features int[0,5] A1;
//features int[0,5] A2;

int main(void) {
  int w = [0,9];	
  int x = w;
		
  int y = [0,9];
  int z = y;
  
  while ([0,1]) {
    if ([0,1]) {
      ++w; ++x;
    } else {
      --y; --z;
    }
  }
	
  assert(w+y == x+z);
  return 0;
}
