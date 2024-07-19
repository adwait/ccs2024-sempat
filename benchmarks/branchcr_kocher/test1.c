
#include "common.h"

void test1 (int idx, itype * a, itype temp_) {
    if (idx < SIZE) {
        temp_ = a[idx]*SCALAR;
    }
}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test1(16, publicarray1, temp);
    
    return 0;
}