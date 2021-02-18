#include <stdio.h>
#include <string.h>
#include <stdint.h> //SIZE_MAX from here

int stringCompare(const char* s1, const char* s2) ;


int main(int argc, char** argv){
    unsigned short int nondet_ushortint();
    unsigned short int size_str1 = nondet_ushortint();
    unsigned short int size_str2 = nondet_ushortint();

    __CPROVER_assume(5 > size_str1 && size_str1 > 1); //size_str1 = 4, 3, 2
    __CPROVER_assume(5 > size_str2 && size_str2 > 1); //size_str2 = 4, 3, 2

    char str1[size_str1];
    char str2[size_str2];
    char nondet_char();


    for(int j = 0; j < size_str1 - 1; j++){
        str1[j] = 'b';
    }

    for(int j = 0; j < size_str2 - 1; j++){
        str2[j] = nondet_char();
        __CPROVER_printf("String123 %d\n", str2[j]);
    }

    __CPROVER_assume(str1[size_str1-1] == '\0'); 
    __CPROVER_assume(str2[size_str2-1] == '\0'); 

    stringCompare(str1,str2);
}


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

    //CASE der giver 4 FAILURES lige nu
    //str1 = "b\0"
    //str2 = "j\0\0\0}"

    //Postcondition
    int same = 1;
    for(int n=0; n<=strlen(begin_s1) && n<=strlen(begin_s2); n++){
        if(begin_s1[n]!=begin_s2[n])
            same = 0;
    }
    if(same)
        __CPROVER_assert(*s1 - *s2 == 0, "Postcondition: same, then return 0");
    else
        __CPROVER_assert(*s1 - *s2 != 0, "Postcondition: different, then return != 0"); //out out bounds fejl får både s1 og s2
    
    __CPROVER_printf("\ns1 offset: %d:\n", __CPROVER_POINTER_OFFSET(s1)); //offset siger 0 for denne case
    __CPROVER_printf("s2 offset: %d:\n", __CPROVER_POINTER_OFFSET(s2)); //offset siger 0 for denne case
    //checket der bliver genereret er: 
    //OBJECT_SIZE(s1) >= 1ul + (unsigned long int)POINTER_OFFSET(s1) && POINTER_OFFSET(s1) >= 0l || DYNAMIC_OBJECT(s1)
    //Så object size må være = 0. Det giver ikke så meget mening...

    return *s1 - *s2; //out out bounds fejl får både s1 og s2
}


//Run Command: cbmc stringCompare.c --bounds-check --pointer-check --unwind 5 --unwinding-assertions --trace
