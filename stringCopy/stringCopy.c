#include <string.h>
#include <stdint.h>

void stringCopy(char* dest, const char* src) {
    __CPROVER_precondition(strlen(dest) >= strlen(src), "Precondition: dest big enough");
    __CPROVER_precondition(SIZE_MAX > strlen(dest), "Precondition: dest not overflow");
    __CPROVER_precondition(__CPROVER_POINTER_OBJECT(dest) != __CPROVER_POINTER_OBJECT(src), "Precondition: point to different objects");
    __CPROVER_precondition(src[strlen(src)] == '\0', "Precondition: src \0 terminated");

    int i = 0;
    int srcStrlen = strlen(src);
    int destStrlen = strlen(dest);

    char* destcopy = dest;
    char* srccopy = src;


    while (i < srcStrlen) {
       *destcopy = *srccopy;
        i = i + 1;
        srccopy = srccopy + 1;
        destcopy = destcopy + 1;
    }

    *destcopy = *srccopy; 

    //Postcondition
    for(int n=0; n<=strlen(src); n++){
        __CPROVER_assert(src[n]==dest[n], "Postcondition: copy correct");
    }
}

int PROOF_HARNESS(){
    unsigned short int size_dest;
    __CPROVER_assume(5 > size_dest && size_dest > 0); 

    char dest[size_dest];
    dest[size_dest-1]='\0';

    unsigned short int size_src; 
    __CPROVER_assume(5 > size_src && size_src > 0); 
    char src[size_src];
    src[size_src-1]='\0';

    for(int i=0; i<size_dest-1; i++){
        __CPROVER_assume(dest[i] != '\0');
    }
    __CPROVER_assume(size_dest >= size_src);

    stringCopy(dest,src);
}

//Run Command: cbmc arrayMax.c --function PROOF_HARNESS --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check --unwind 5 --unwinding-assertions

/*
    Reflections
        Loop invariant osv. virker ikke relevant
        Fejler hvis src array længde = 1. (Out of bounds linje 67)
*/