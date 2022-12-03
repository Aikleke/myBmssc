#include <iostream>
#include<time.h>
#include<ctime>
using namespace std;
int main() {
    double s=clock(),e;
    int j=0;
    for (int i = 0; i < 100000000; ++i) {
        j++;
    }
    e=clock();
    cout<<(e-s)/CLOCKS_PER_SEC;
    return 0;
}
