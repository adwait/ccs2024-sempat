#include "common.h"


void test4 (int idx, itype * a, itype temp_) {
    if (idx < SIZE/2) {
        temp_ = a[idx<<1]*SCALAR;
    }
}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test4(SIZE, publicarray1, temp);
    
    return 0;
}