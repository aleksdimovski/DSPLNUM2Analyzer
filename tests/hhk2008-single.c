// Source: Thomas A. Henzinger, Thibaud Hottelier, Laura Kovacs: "Valigator:
// A verification Tool with Bound and Invariant Generation", LPAR 2008

//features int[0,5] A1;
//features int[0,5] A2;
//features int[0,5] A3;

#include "assert.h"

int main() {
    int res = [-9,9]; //__VERIFIER_nondet_int();
	int cnt = [-9,9]; //__VERIFIER_nondet_int();
	
    
    int a, b;

    a = res;
    b = cnt;
    while (cnt > 0) {
		cnt = cnt - 1;
		res = res + 1;
    }
    assert(res == a + b);
    return 0;
}
