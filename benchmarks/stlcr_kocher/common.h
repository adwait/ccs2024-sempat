
#ifndef __COMMON_H__
#define __COMMON_H__

#include <stdint.h>
#include <stddef.h>

#define SIZE 16
#define SCALAR 0x0000cafe
#define SECRET 0xdeadbeef

#define TEMP \
    itype temp = 0;


#define PUBLICARRAY \
    itype publicarray1[SIZE]; \
    publicarray1[0] = 0; \
    publicarray1[1] = 1; \
    publicarray1[2] = 2; \
    publicarray1[3] = 3; \
    publicarray1[4] = 4; \
    publicarray1[5] = 5; \
    publicarray1[6] = 6; \
    publicarray1[7] = 7; \
    publicarray1[8] = 8; \
    publicarray1[9] = 9; \
    publicarray1[10] = 10; \
    publicarray1[11] = 11; \
    publicarray1[12] = 12; \
    publicarray1[13] = 13; \
    publicarray1[14] = 14; \
    publicarray1[15] = 15; 

#define SECRETARRAY \
    itype secretarray[1]; \
    secretarray[0] = SECRET;

typedef uint32_t itype;
    
#endif