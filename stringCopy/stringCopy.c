#include <string.h>
#include <stdint.h>

int HELP_same_chars(const char* s1, const char* s1);

void stringCopy(char* dest, const char* src) {
    __CPROVER_precondition(5 > strlen(dest)+1 && strlen(dest)+1 > 0, "Precondition: assumes 5 > size_dest > 0");
    __CPROVER_precondition(5 > strlen(src)+1 && strlen(src)+1 > 0, "Precondition: assumes 5 > size_src > 0");
    __CPROVER_precondition(dest[strlen(dest)] == '\0', "Precondition: assumes dest \0 terminated> 0");
    __CPROVER_precondition(src[strlen(src)] == '\0', "Precondition: assumes src \0 terminated");
    __CPROVER_precondition(strlen(dest) >= strlen(src), "Precondition: dest big enough");

    __CPROVER_precondition(SIZE_MAX > strlen(dest), "Precondition: dest not overflow");
    __CPROVER_precondition(__CPROVER_POINTER_OBJECT(dest) != __CPROVER_POINTER_OBJECT(src), "Precondition: point to different objects");

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
    __CPROVER_postcondition(HELP_same_chars(src, dest), "Postcondition: copy correct");
}

void PROOF_HARNESS(){
    unsigned int size_dest;
    unsigned int size_src; 

    char dest[size_dest];
    char src[size_src];

    __CPROVER_assume(5 > size_dest && size_dest > 0); 
    __CPROVER_assume(5 > size_src && size_src > 0); 
    __CPROVER_assume(dest[size_dest-1]=='\0');
    __CPROVER_assume(src[size_src-1]=='\0');
    __CPROVER_assume(strlen(dest) >= strlen(src));


    stringCopy(dest,src);

    __CPROVER_postcondition(HELP_same_chars(src, dest), "Postcondition: copy correct");
}

int HELP_same_chars(const char* s1, const char* s1){
    for(int n=0; n<=strlen(s1); n++){
        if(s1[n]!=s2[n])
            return 0;
    }
    return 1;
}

//Run Command: cbmc stringCopy.c --function PROOF_HARNESS --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check --unwind 5 --unwinding-assertions

/*
    Reflections
        Loop invariant osv. virker ikke relevant
        Fejler hvis src array længde = 1. (Out of bounds linje 67)
*/