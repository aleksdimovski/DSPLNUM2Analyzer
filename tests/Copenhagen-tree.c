/*
 * Date: 2012-02-18
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
features int[-9,9] x;
features int[-9,9] y;
//features int[0,4] A3;

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int oldx;
	//x = [-9,9]; // __VERIFIER_nondet_int();
	//y = [-9,9]; // __VERIFIER_nondet_int();
	
	
	while (x >= 0 && y >= 0) {
		oldx = x;
		x = y - 1;
		y = oldx - 1;
	}
	
	assert(x+y<=0); 
	
	return 0;
}
