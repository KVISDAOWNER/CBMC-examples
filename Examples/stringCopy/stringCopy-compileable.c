#include <stdio.h>
#include <string.h>
#include <stdint.h>

void stringCopy(char* dest, const char* src);
int main(int argc, char** argv){
    unsigned short int nondet_ushortint();

    
    char dest[7] = "123456";
    dest[7-1]='\0';

    char src[] = "1234";

    src[5-1]='\0';

    printf("Dest pre: %s\n", dest);
    printf("Src pre: %s\n", src);
    stringCopy(dest,src);
    printf("Dest post: %s\n", dest);
    printf("Src post: %s\n", src);

}
    
void stringCopy(char* dest, const char* src) {
    size_t i = 0;
    size_t srcStrlen = strlen(src);
    size_t destStrlen = strlen(dest);

    char* destcopy = &(dest[0]);
    const char* srccopy = &(src[0]);

    while (i < srcStrlen) {
       *destcopy = *srccopy;
        i = i + 1;
        srccopy = srccopy + 1;
        destcopy = destcopy + 1;
    }
    *destcopy = *srccopy;
}