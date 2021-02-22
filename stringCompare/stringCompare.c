#include <string.h>
#include <stdint.h> //SIZE_MAX from here

int stringCompare(const char* s1, const char* s2) {
    __CPROVER_precondition(SIZE_MAX > strlen(s1), "Precondition: s1 not overflow");
    __CPROVER_precondition(SIZE_MAX > strlen(s2), "Precondition: s2 not overflow");
    __CPROVER_precondition(s1[strlen(s1)] == '\0', "Precondition: s1 \0 terminated");
    __CPROVER_precondition(s2[strlen(s2)] == '\0', "Precondition: s2 \0 terminated");

    const char* begin_s1 = s1;
    const char* begin_s2 = s2;

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
    for(int n=0; n<=strlen(begin_s1) && n<=strlen(begin_s2); n++){
        if(begin_s1[n]!=begin_s2[n])
            same = 0;
    }
    if(same)
        __CPROVER_assert(*s1 - *s2 == 0, "Postcondition: same, then return 0");
    else
        __CPROVER_assert(*s1 - *s2 != 0, "Postcondition: different, then return != 0");


    return *s1 - *s2; 
}


void PROOF_HARNESS(){
    unsigned short int size_str1, size_str2;

    __CPROVER_assume(5 > size_str1 && size_str1 > 0);
    __CPROVER_assume(5 > size_str2 && size_str2 > 0);

    char str1[size_str1];
    char str2[size_str2];

    str1[size_str1-1] = '\0'; 
    str2[size_str2-1] = '\0'; 

    stringCompare(str1,str2);
}

//Run Command: cbmc stringCompare.c --function PROOF_HARNESS --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check --unwind 5 --unwinding-assertions --trace
