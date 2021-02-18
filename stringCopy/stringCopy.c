#include <stdio.h>
#include <string.h>
#include <stdint.h>

void stringCopy(char* dest, const char* src) ;
void stringCopy1(char* dest, const char* src) ;
int strlen2(const char* str) ;

int main(int argc, char** argv){
    unsigned short int nondet_ushortint();

    unsigned short int size_dest = nondet_ushortint();
    __CPROVER_assume(5 > size_dest && size_dest > 0); //size_dest = 4, 3, 2, 1
    char dest[size_dest];
    for(int j = 0; j < size_dest - 1; j++){
        dest[j] = "a";
    }
    dest[size_dest-1]='\0';

    unsigned short int size_src = nondet_ushortint(); 
    __CPROVER_assume(5 > size_src && size_src > 1); //size_src = 4, 3, 2
    char src[size_src];
    for(int j = 0; j < size_src - 1; j++){
        src[j] = "b";
    }
    src[size_src-1]='\0';

    for(int i=0; i<size_dest-1; i++){
        __CPROVER_assume(dest[i] != '\0');
    }
    __CPROVER_assume(size_dest >= size_src);

    __CPROVER_printf("\nCASE");
    __CPROVER_printf("Size of dest array: %d", (size_dest));
    __CPROVER_printf("Size of src array: %d\n", (size_src));

    stringCopy(dest,src);
}

    
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

    __CPROVER_printf("\ni: %d", i);
    __CPROVER_printf("srcStrlen: %d", srcStrlen);
    __CPROVER_printf("\n");
    while (i < srcStrlen) {
       *destcopy = *srccopy;
        i = i + 1;
        srccopy = srccopy + 1;
        destcopy = destcopy + 1;
    }
    __CPROVER_printf("\n Destcopy offset: %d \n Srccopy offset: %d" ,__CPROVER_POINTER_OFFSET(destcopy), __CPROVER_POINTER_OFFSET(srccopy));
    __CPROVER_printf("\n Destcopy strlen: %d \n Srccopy strlen: %d", destStrlen, srcStrlen);


    *destcopy = *srccopy; //CBMC siger out of bounds. Men det er det ikke? 
    //Den generer dette check
    // OBJECT_SIZE(srccopy) >= 1ul + (unsigned long int)POINTER_OFFSET(srccopy) && POINTER_OFFSET(srccopy) >= 0l || DYNAMIC_OBJECT(srccopy)
    //Som failer hvis src kun indeholder \0 



    //Postcondition
    for(int n=0; n<=strlen(src); n++){
        __CPROVER_assert(src[n]==dest[n], "Postcondition: copy correct");
    }
}

//Run Command: cbmc stringCopy.c --bounds-check --pointer-check --unwind 5 --unwinding-assertions

/*
    Reflections
        Loop invariant osv. virker ikke relevant
        Fejler hvis src array længde = 1. (Out of bounds linje 67)
*/