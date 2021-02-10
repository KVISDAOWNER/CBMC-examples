#include <stdio.h>
#include <string.h>
#include <stdint.h>

void stringCopy(char* dest, const char* src) ;

int main(int argc, char** argv){
    char src[] = "luder";
    char dest[6];
    //stringCopy(dest, src);
    stringCopy(dest,src);
}


    /*@ requires validDest: valid_string(dest);
    requires validReadSrc: valid_read_string(src);
    requires destLargest: strlen(dest) >= strlen(src);
    requires noDestOverflow: SIZE_MAX > strlen(dest);
    requires separatedStrings: \separated(src + (0 .. strlen(src)), dest + (0 .. strlen(dest))) ;
    requires nullCharEnd: src[strlen(src)] == '\0';

    assigns *(dest + (0 .. strlen(src)));

    ensures copied: \forall integer k; 0 <= k <= strlen(src) ==> dest[k] == src[k];
    ensures stillValidDest: *(dest + strlen(src)) == '\0';
    */
    
void stringCopy(char* dest, const char* src) {
    int i = 0;
    int srcStrlen = strlen(src);
    int destStrlen = strlen(dest);

    char* destcopy = &(dest[0]);
    char* srccopy = &(src[0]);

    /*@ loop invariant validRange: 0 <= i <= srcStrlen <= destStrlen ;
        loop invariant intermediateCopied: \forall integer k; 0 <= k < i ==> dest[k] == src[k];
        loop invariant srcPos: src + i == srccopy ;
        loop invariant destPos: dest + i == destcopy ;
        loop assigns i, srccopy, destcopy, *(dest + (0 .. srcStrlen - 1));
    */

    while (i < 10) {
       *destcopy = *srccopy;
        i = i + 1;
        srccopy = srccopy + 1;
        destcopy = destcopy + 1;
    }
    //*destcopy = *srccopy;
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
        Lortet kører uendeligt
*/