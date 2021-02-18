#include <stdio.h>
#include <string.h>
#include <stdint.h> //SIZE_MAX from here

int stringCompare(const char* s1, const char* s2) ;


int main(int argc, char** argv){
    char dest[] = "12345";
    char src[] = "hallo";
    stringCompare(dest,src);
}


int stringCompare(const char* s1, const char* s2) {
    __CPROVER_precondition(SIZE_MAX > strlen(s1), "Precondition: s1 not overflow");
    __CPROVER_precondition(SIZE_MAX > strlen(s2), "Precondition: s2 not overflow");
    __CPROVER_precondition(s1[strlen(s1)] == '\0', "Precondition: s1 \0 terminated");
    __CPROVER_precondition(s2[strlen(s2)] == '\0', "Precondition: s2 \0 terminated");

    if (s1 == s2)
        return 0;
    int i = 0;
   

    while (*s1 == *s2)
    {
        ++i;
        if (*s1 == '\0')
            return 0;
        ++s1;
        ++s2;
    }

    //Postcondition
    int same = 1;
    for(int n=0; n<=strlen(s1); n++){
        if(s1[n]!=s2[n])
            same = 0;
    }
    if(same)
        __CPROVER_assert(*s1 - *s2 == 0, "Postcondition: same then == 0");
    else
        __CPROVER_assert(*s1 - *s2 != 0, "Postcondition: different then != 0");


    return *s1 - *s2;
}


//Run Command: cbmc stringCompare.c --bounds-check --pointer-check 
