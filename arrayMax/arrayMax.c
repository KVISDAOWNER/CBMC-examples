#include <stdint.h> //SIZE_MAX from here


int arrayMax(int* arr, int size) {
    __CPROVER_precondition(size > 0, "Precondition: size is above 0");

    int result = arr[0];
    int i = 0;

    while (i < size) {
        if (arr[i] > result) 
            result = arr[i];
        i++;
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

void PROOF_HARNESS(){
    unsigned short int size;
    __CPROVER_assume(5 > size && size > 0);
    int arr[size];
    arrayMax(arr, size);
}


//Run Command: cbmc arrayMax.c --function PROOF_HARNESS --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check --unwind 5 --unwinding-assertions


/*
Ting der ikke tjekkes, i.f.t. frama-c:
    \assigns nothing
    loop variant

    
/Reflections
    Giver loop invarianter overhovedet mening?
    Vi er rimelig sikre på at loop varianter er ligegyldige (i og med man bruger bounded model checking)
*/