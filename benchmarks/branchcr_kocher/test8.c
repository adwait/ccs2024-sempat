#include "common.h"

void test8 (int idx, itype * a, itype temp_) {    
    temp_ = a[idx < SIZE ? idx : 0] * SCALAR;

}


int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test8 (SIZE, publicarray1, temp);
    
    return 0;
}