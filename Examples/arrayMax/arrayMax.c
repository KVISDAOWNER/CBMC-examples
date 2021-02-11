#include <stdio.h>
#include <assert.h>
#include <stdint.h> //SIZE_MAX from here

int arrayMax(int* arr, int size);

int main(int argc, char** argv){

    unsigned short int nondet_ushortint();
    unsigned short int size = nondet_ushortint();
    __CPROVER_assume(5 > size && size > 0);
    int arr[size];
    __CPROVER_printf("Print shit: ");
    __CPROVER_printf(__CPROVER_OBJECT_SIZE(arr));
    arrayMax(arr, size);
}


int arrayMax(int* arr, int size) {
    __CPROVER_precondition(size > 0, "Precondition: size is above 0");

    int result = arr[0];
    int i = 0;

    for(int n=0; n<i; n++){ //Never enters
        //__CPROVER_assert(result>=arr[n], "loop invariant: pre");
    }
    while (i < size) {
        for(int n=0; n<i; n++){
        //__CPROVER_assert(result>=arr[n], "loop invariant: at");
        }
        if (arr[i] > result) 
            result = arr[i];

        i++;
    }
    for(int n=0; n<i; n++){
        //__CPROVER_assert(result>=arr[n], "loop invariant: post");
    }

    //Postcondition
    int exists = 0;
    for(int n = 0; n < size; n++){
        if(arr[n] == result)
            exists = 1;
        __CPROVER_assert(result >= arr[n], "Postcondition: result greater than"); 
    }
    __CPROVER_assert(exists==1, "Postcondition: result exists in array"); 


    return result;
}

//Run Command: cbmc arrayMax.c --bounds-check --pointer-check 


/*
Ting der ikke tjekkes, i.f.t. frama-c:
    \assigns nothing
    loop variant

    
/Reflections
    Giver loop invarianter overhovedet mening?
    Vi er rimelig sikre på at loop varianter er ligegyldige (i og med man bruger bounded model checking)
*/