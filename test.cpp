//
// Created by 东风课 on 2022/12/4.
//
#include<ctime>
#include<iostream>
using namespace std;
int main(){
    double  i=1999;
    double  sum=0;
    double ssum=0;
    double s=clock(),e;
    for (int j = 0; j < 100000000; ++j) {
        sum+=i;
        ssum+=j*i;
    }
    e=clock();
    cout<<(e-s)/CLOCKS_PER_SEC<<endl;
}