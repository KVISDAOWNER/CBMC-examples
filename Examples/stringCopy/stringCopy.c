#include <stdio.h>
#include <string.h>
#include <stdint.h>

void stringCopy(char* dest, const char* src) ;
void stringCopy1(char* dest, const char* src) ;
int strlen2(const char* str) ;

int main(int argc, char** argv){
    char dest[] = "12345";
    char src[] = "hallo";
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

    char* destcopy = &(dest[0]);
    char* srccopy = &(src[0]);

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



void stringCopy1(char* dest, const char* src) {

    while(*src!='\0'){
        *dest=*src;
        dest++;
        src++;
    }
    *dest='\0';
}
//Run Command: cbmc stringCopy.c --bounds-check --pointer-check 

/*
    Reflections
        Loop invariant osv. virker ikke relevant
*/