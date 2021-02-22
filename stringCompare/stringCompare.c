#include <string.h>
#include <stdint.h> //SIZE_MAX from here

int HELP_same_chars(const char* s1, const char* s2);

int stringCompare(const char* s1, const char* s2) {
    __CPROVER_precondition(5 > strlen(s1)+1 && strlen(s1)+1 > 0, "Precondition: assumes 5 > size_s1 > 0");
    __CPROVER_precondition(5 > strlen(s2)+1 && strlen(s2)+1 > 0, "Precondition: assumes 5 > size_s2 > 0");
    __CPROVER_precondition(s1[strlen(s1)] == '\0', "Precondition: assumes s1 \0 terminated");
    __CPROVER_precondition(s2[strlen(s2)] == '\0', "Precondition: assumes s2 \0 terminated");
    __CPROVER_precondition(SIZE_MAX > strlen(s1), "Precondition: s1 not overflow");
    __CPROVER_precondition(SIZE_MAX > strlen(s2), "Precondition: s2 not overflow");

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

    if(HELP_same_chars(begin_s1, begin_s2))
        __CPROVER_postcondition(*s1 - *s2 == 0, "Postcondition: same, then return 0");
    else
        __CPROVER_postcondition(*s1 - *s2 != 0, "Postcondition: different, then return != 0");


    return *s1 - *s2; 
}

int HELP_same_chars(const char* s1, const char* s2){
    for(int n=0; n<=strlen(s1) && n<=strlen(s2); n++){
        if(s1[n]!=s2[n])
            return 0;
    }
    return 1;
}

void PROOF_HARNESS(){
    unsigned int size_s1, size_s2;

    char s1[size_s1];
    char s2[size_s2];

    __CPROVER_assume(5 > size_s1 && size_s1 > 0);
    __CPROVER_assume(5 > size_s2 && size_s2 > 0);
    __CPROVER_assume(s1[size_s1-1] == '\0');
    __CPROVER_assume(s2[size_s2-1] == '\0');

    int res = stringCompare(s1,s2);

    if(HELP_same_chars(s1, s2))
        __CPROVER_postcondition(res == 0, "Postcondition: same, then return 0");
    else
        __CPROVER_postcondition(res != 0, "Postcondition: different, then return != 0");

}

//Run Command: cbmc stringCompare.c --function PROOF_HARNESS --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check --unwind 5 --unwinding-assertions --trace
