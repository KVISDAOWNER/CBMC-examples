#include <stdint.h> //SIZE_MAX from here

int HELP_exists_in_arr(const int* arr, const unsigned int size, const int e);
int HELP_element_greater_than_or_eq(const int* arr, const unsigned int size, const int e);

int arrayMax(int* arr, const unsigned int size) {
    __CPROVER_precondition(5 > size && size > 0, "Precondition: assumes 5 > size > 0");  
    int result = arr[0];
    int i = 0;

    while (i < size) {
        if (arr[i] > result) 
            result = arr[i];
        i++;
    }

    __CPROVER_postcondition(HELP_exists_in_arr(arr, size, result), "Postcondition: result exists in array"); 
    __CPROVER_postcondition(HELP_element_greater_than_or_eq(arr, size, result), "Postcondition: result greater than"); 

    return result;
}

void PROOF_HARNESS(){
    unsigned int size;
    int arr[size];

    __CPROVER_assume(5 > size && size > 0);

    int max = arrayMax(arr, size);
    __CPROVER_postcondition(HELP_exists_in_arr(arr, size, max), "Postcondition: returned max exists in array"); 
    __CPROVER_postcondition(HELP_element_greater_than_or_eq(arr, size, max), "Postcondition: returned max greater than"); 

}

int HELP_exists_in_arr(const int* arr, const unsigned int size, const int e){
    for(int n = 0; n < size; n++){
        if(arr[n] == e)
            return 1;
    }
    return 0;
}

int HELP_element_greater_than_or_eq(const int* arr, const unsigned int size, const int e){
    for(int n = 0; n < size; n++){
        if(e < arr[n])
            return 0;
    }
    return 1;
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