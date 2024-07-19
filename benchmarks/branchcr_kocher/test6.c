#include "common.h"

void test6 (int idx, itype * a, itype temp_) {
    const int SIZE_MASK = SIZE - 1;
    
    if ((idx & SIZE_MASK) == idx) {
        temp_ = a[idx] * SCALAR;
    }
}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test6(SIZE, publicarray1, temp);
    
    return 0;
}