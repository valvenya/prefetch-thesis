#include <stdlib.h>
#include <stdio.h>

int main() {
    int arr[100];
    int arr2[100];
    int i = 0;
    int sum = 0;

    for (i = 0; i < 100; i++) {
        arr[i] = i;
        arr2[i] = rand() % 100;
    }

    for (i = 0; i < 100; i++) {
        sum += arr[arr2[i]];
    }

    printf("%d\n", sum);
    return 0;
}