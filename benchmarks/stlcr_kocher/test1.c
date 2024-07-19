
#include "common.h"

// case 2 from Haunted
void test1 (int idx, itype * a, itype temp_) {    
    idx = idx & (SIZE - 1);
    temp_ &= a[idx] * SCALAR;

}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test1 (SIZE, publicarray1, temp);
    
    return 0;

}