#include <stdio.h>
#include <assert.h>
#include <math.h>

int arrayMax(int* arr, int size);

int main(int argc, char** argv){
    int arr[10] = {1,2,3,4,5,6,7,8,9,10};
    arrayMax(arr, 10);
}


int arrayMax(int* arr, int size) {
    __CPROVER_precondition(size > 0, "Precondition: Size positive");
    int result = arr[0];
    int i = 0;

    while (i < size) {

        if (arr[i] > result) 
            result = arr[i];

        i++;
    }

    for(int n = 0; n < size; n++){
        __CPROVER_assert(result >= arr[n], "Postcondition: Result greater than"); 
    }
    return result;
}

//cbmc arrMax.c --bounds-check --pointer-check 