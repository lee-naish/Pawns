// top level for isort.pns could redo in Pawns
// demonstrates Pawns calling extern function

#include <stdlib.h>
#include <stdio.h>
#include "pawns.h"
#include "isort.h"

// see array.pns: arrays are a block of words, the first being the size
void
print_array(array a) {
    intptr_t size = *(intptr_t*)a, *ep = (intptr_t*)a + 1;
    int j;
    printf("print_array %d %d\n", (int) a, size);
    for(j=0; j < size; j++) {
        print_int((int) *ep++);
    }
}

void
main() {
    test_isort();
    exit(0);
}
