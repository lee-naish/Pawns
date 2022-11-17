// prototype array support for pawns
// Old - use array.pns now (though no inline pragma)
#include "array_adt.h"
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>


// (generic) arrays are pointers to a block of words (void*), the first
// is the number of elements, the rest are the elements of the array

// malloc space for size (stored with array) + elements and initialise
array
array_new(int size, void *initval) {
    int i;
    void *vp, **vpp; // note ptr to ptr so vpp++ does the right thing
    if (size < 0)
        size = 0;
    vp = malloc((size+1)*sizeof(void*));
    if (!vp) {
        fprintf(stderr, "Malloc of array failed\n");
        exit(1);
    }
    vpp = (void **) vp; // vpp points to first void* in block
    *vpp++ = (void*) size;
    for (i=0; i < size; i++)
        *vpp++ = initval;
    return (array) vp;
}

// returns ptr to nth array element
// XXX inline this
void **array_nthp(array arr, int n) {
    // arr != NULL, we hope XXX
    return ((void**)arr + n + 1);  // ptr arith, cast is important
}

// returns size of array
// XXX inline this
int
array_size(array arr) {
    // arr != NULL, we hope XXX
    return (int) *((intptr_t*) arr);
}


// void array_free(void *arr);
