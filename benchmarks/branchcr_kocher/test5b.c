#include "common.h"

void test5b (int idx, itype * a, itype temp_) {
    int i;
    if (idx < SIZE) {
        for (i = idx-1; i>=0; i--) {
            temp_ = a[i] * SCALAR;
        }
    }
}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test5b(SIZE+1, publicarray1, temp);
    
    return 0;
}