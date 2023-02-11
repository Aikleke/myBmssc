#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <string>
#include<string.h>
#include<sstream>
#include<iomanip>
#include <time.h>
#include <cmath>
#include<random>
#include<vector>
#include<algorithm>
using namespace std;
#define precision 1
#define PopNum 15                                        //种群大小
#define DEBUG2
#define MAXNUM 99999999999999
#define NUM1    50
#define DEVIATION    0.000001
#define DATASETNUM 16
#define CLUTERNUM 10
#define RUNS 10
#define RANDOM_POPULATION_RATIO 1
typedef double LL;
double StartTime, FinishTime, Runtime;
int Runs;        //每个算例运行次数

int *BestS;
int *CluLen;    //每个cluster的size，swap前后size不变
LL Objective;
LL ObjBest;

//N,K,D在main函数里给出
int N;        //the number of vertices
int K;        //the number of clusters
int D;        //dimensions
int Type;        //算例类型
LL **Point;    //顶点坐标，坐标维度为D
LL **MatrixNK;
LL *ObjClu;    //每个cluster的目标值，没有除以该cluster的size
LL **DisSquare;    //欧几里得空间的任意两点的欧式距离的平方

/**
 * 为了进行贪心构造中的距离排序 的类
 */
class Node{
public:
    LL dis;
    int index;
    Node(LL dis,int index){
        this->dis=dis;
        this->index=index;
    }
    bool static increase(const Node &node1,const Node &node2){
        return node1.dis<node2.dis;
    }
};
// for random
class Random {
public:
    using Generator = mt19937;
    Random(int seed) : rgen(seed) {}
    Random() : rgen(generateSeed()) {}
    static int generateSeed() {
        return static_cast<int>(std::time(nullptr) + std::clock());
    }

    Generator::result_type operator()() { return rgen(); }

    // pick with probability of (numerator / denominator).
    bool isPicked(unsigned numerator, unsigned denominator) {
        return ((rgen() % denominator) < numerator);
    }

    // pick from [min, max).
    int pick(int min, int max) {
        return ((rgen() % (max - min)) + min);
    }
    // pick from [0, max).
    int pick(int max) {
        return (rgen() % max);
    }
    Generator rgen;
};
Random better_rand;
std::random_device rd;
std::mt19937 g(rd());

//for the memetic algorithm
typedef struct Population{
    int *p;
    LL cost;
}Population;
Population *Pop;
Population Child;        //子代
Population child_update;
int **arr1;
int **arr2;
int *len;
int *len2;
int *match;
int *flagC1;
int *flagC2;
int *flagV;
int *unassV;
int *addressUnaV;

//for responsive threshold search
double TR;                    //threshold ratio
double TA, TB, TC;            //the parameters
LL ThreshT;                //threshold T
LL ObjP;
int RTS_ITER;                //每代，RTS迭代次数
int *randN;
int *randK;
int *flagN;
int *flagK;

/**
 * 新增数据结构
 */
 //距离排序数据结构。 为了方便进行贪心构造
vector<vector<Node>> nodeDisMatrix;


double MaxTimes[DATASETNUM][CLUTERNUM][RUNS]; //数据集数量16*簇种类10*跑的次数10
void initialing(string file)
{
    double dd;
    int row = 0, col = 0;
    string line;
    stringstream ss;
    fstream fs(file);
    if (!fs)
    {
        cout << "error open, File_Name " << file << endl;
        getchar();
        exit(1);
    }
    Point = new LL*[N];
    for (int index = 0; index < N; index++)
    {
        Point[index] = new LL[D];
    }
    while (getline(fs, line))
    {
        col = 0;
        ss << line;
        while (ss >> dd)            //算例文件经过格式化处理，每列数据以制表符分割
        {
            Point[row][col++] = dd;
        }
        row++;
#ifdef DEBUG1
        for (int i = 0; i < D; i++)
        {
            cout << Point[row - 1][i] << ",";
        }
        cout << endl;
#endif
        ss.clear();
    }

    BestS = new int[N];
    DisSquare = new LL*[N];
    for (int i = 0; i < N; i++)
    {
        DisSquare[i] = new LL[N];
    }
    for (int i = 0; i < N; i++)
    {
        for (int j = 0; j < N; j++)
            DisSquare[i][j] = 0;
    }
    Pop = new Population[PopNum];
    for (int i = 0; i < PopNum; i++)
        Pop[i].p = new int[N];
    Child.p = new int[N];
    for (int i = 0; i < N; i++)
    {
        for (int j = i + 1; j < N; j++)
        {
            int dimens = 0;
            while (dimens < D)
            {
                DisSquare[i][j] += (Point[i][dimens] - Point[j][dimens])*(Point[i][dimens] - Point[j][dimens])*precision;
                dimens++;
            }
            DisSquare[j][i] = DisSquare[i][j];
        }
    }
#ifdef DEBUG
    cout<<"打印距离排序数组"<<endl;
#endif
    for(int i=0;i<N;i++){
        vector<Node> tmp;
        nodeDisMatrix.emplace_back(tmp);
    }
    for(int i=0;i<N;i++){
        for(int j=0;j<N;j++) {
            nodeDisMatrix[i].emplace_back(Node(DisSquare[i][j],j));
        }
        sort(nodeDisMatrix[i].begin(),nodeDisMatrix[i].end(),Node::increase);
#ifdef DEBUG
        for(int j=0;j<N;j++) {
            cout<<nodeDisMatrix[i][j].dis<<" "<<nodeDisMatrix[i][j].index<<"-- ";
        }
        cout<<endl;
#endif
    }
    fs.close();
}

void allocateMemory()
{
    MatrixNK = new LL*[N];
    for (int i = 0; i < N; i++)
    {
        MatrixNK[i] = new LL[K];
    }
    CluLen = new int[K];
    ObjClu = new LL[K];
    randN = new int[N];
    randK = new int[K];
    for(int i=0;i<N;i++){
        randN[i]=i;
    }
    for(int i=0;i<K;i++){
        randK[i]=i;
    }
    flagN = new int[N];
    flagK = new int[K];
    arr1 = new int*[K];
    arr2 = new int*[K];
    len = new int[K];
    len2 = new int[K];
    match = new int[K];
    flagC1 = new int[K];
    flagC2 = new int[K];
    flagV = new int[N];
    unassV = new int[N];
    addressUnaV = new int[N];
    for (int i = 0; i < K; i++)
    {
        arr1[i] = new int[N];
        arr2[i] = new int[N];
    }
    child_update.p = new int[N];
}

void readTimeFile(string file)
{
    string line;
    stringstream ss;
    fstream fs(file);
    int col1, col2, col3;
    double dd;
    col1 = 0;
    //col1 = 14;
    col2 = 0;

    cout << "file=" << file << endl;
    if (!fs)
    {
        cout << "error open, File_Name: " << file << endl;
        getchar();
        exit(1);
    }
    while (getline(fs, line))
    {
        col3 = 0;
        ss << line;
        while (ss >> dd)            //算例文件经过格式化处理，每列数据以制表符分割
        {
            MaxTimes[col1][col2][col3++] = dd;
        }
        col2++;
        if (col2%CLUTERNUM == 0)
        {
            col1++;
            col2 = 0;
        }
        ss.clear();
    }
#ifdef DEBUG
    for (int i = 0; i < col1; i++)
    {
        for (int k = 0; k < CLUTERNUM; k++)
        {
            for (int j = 0; j < RUNS; j++)
                cout << "i=" << i << ",k=" << k << ",j=" << j << "," << MaxTimes[i][k][j] << " " << endl;
            cout << endl;
        }
    }
    cout << endl;
#endif
    fs.close();
}
/**
 随机初始化函数
 可以改进：
 1.随机初始化方法
 2.rand函数
 */
void randomConstruction(int *ss)
{
    shuffle(randN, randN+N, g );
    int minLen=N/K;
    int index=0;
    for(int i=0;i<K;i++){
        if(i<N%K){
            CluLen[i]=minLen+1;
            for(int j=0;j<minLen+1;j++){
                int ver=randN[index++];
                ss[ver]=i;
            }
        }else{
            CluLen[i]=minLen;
            for(int j=0;j<minLen;j++){
                int ver=randN[index++];
                ss[ver]=i;
            }
        }
    }
}
/**
 * 一种贪心的构造方法
 * 1.在所有点中 随机选择初始点
 * 2.选择k or k+1个 距离当前点最近的点，将入到这个组中
 *
 */
void greedyConstruction(int *ss)
{
//    打乱节点排列顺序
    shuffle(randN, randN+N, g );
    int minLen=N/K;
    int index=0;
    vector<int> flag(N);
    int curGroup=0;

    for(int i=0;i<K;i++){
        if(i<N%K)
            CluLen[i]=minLen+1;
        else
            CluLen[i] = minLen;
    }
    for(int i=0;i<N;i++){
        if(flag[i]==1) continue;
        if(curGroup==K) continue;
        int j=0;
        for(int k=0;k<CluLen[curGroup];k++){
            while(j<N&&flag[nodeDisMatrix[i][j].index]==1)
                j++;
            flag[nodeDisMatrix[i][j].index]=1;
            ss[nodeDisMatrix[i][j].index]=curGroup;
        }
        curGroup++;
    }
}
//计算目标函数值
double caculateObj(int *ss)
{
    double dd;
    double obj = 0;
    for (int i = 0; i < K; i++)
    {
        dd = 0;
        for (int j = 0; j < N; j++)
        {
            for (int k = j + 1; k < N; k++)
            {
                if (ss[j] == i &&ss[k] == i)
                {
                    dd += DisSquare[j][k];
                }
            }
        }
        dd /= CluLen[i];
        obj += dd;
    }
    return obj;
}

//与之前的xiangjing.lai文章中的gamma矩阵含义相同
void initialMatrixNKAndObjClu(int *ss)
{
    for (int i = 0; i < N; i++)
    {
        for (int j = 0; j < K; j++)
            MatrixNK[i][j] = 0;
    }
    for (int i = 0; i < K; i++)
        ObjClu[i] = 0;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            MatrixNK[i][ss[j]] += DisSquare[i][j];
    for (int i = 0; i < K; i++)
    {
        for (int j = 0; j < N; j++)
        {
            if (ss[j] == i)
            {
                ObjClu[i] += MatrixNK[j][i];
            }
        }
        ObjClu[i] /= 2;
    }
}

void updateMatrixNK(int i, int g0, int g1)
{
    for (int j = 0; j<N; j++)
    {
        if (j != i)
        {
            MatrixNK[j][g0] -= DisSquare[i][j];
            MatrixNK[j][g1] += DisSquare[i][j];
        }
    }
}


void checkMove(double obj, int *ss)
{
    double obj1 = caculateObj(ss);
    if (fabs(obj - obj1)>DEVIATION)
    {
        printf("heer,obj=%6f,obj1=%6f,", obj, obj1);
        cout << "obj!=obj1##############,error,please check the delta value" << endl;
        getchar();
    }
}

double cal_insert_delta(int *ss,int ele,int clu){
    return (ObjClu[ss[ele]] - MatrixNK[ele][ss[ele]]) / (CluLen[ss[ele]] - 1) + (MatrixNK[ele][clu] + ObjClu[clu]) / (CluLen[clu] + 1)
           - (ObjClu[ss[ele]] / CluLen[ss[ele]] + ObjClu[clu] / CluLen[clu]);
}
double cal_swap_delta(int *ss,int ele,int ele2){
    return (MatrixNK[ele2][ss[ele]] - DisSquare[ele][ele2] - MatrixNK[ele][ss[ele]]) / CluLen[ss[ele]] +
           (MatrixNK[ele][ss[ele2]] - DisSquare[ele][ele2] - MatrixNK[ele2][ss[ele2]]) / CluLen[ss[ele2]];
}
void swap_move(int *ss,int ele,int ele2,double delta){
    int temp = ss[ele];
    int temp2 = ss[ele2];
    ss[ele] = temp2;
    ss[ele2] = temp;
    ObjClu[temp] += MatrixNK[ele2][temp] - DisSquare[ele][ele2] - MatrixNK[ele][temp];
    ObjClu[temp2] += MatrixNK[ele][temp2] - DisSquare[ele][ele2] - MatrixNK[ele2][temp2];
    updateMatrixNK(ele, temp, temp2);
    updateMatrixNK(ele2, temp2, temp);
    Objective += delta;
    //Objective= caculateObj(ss);

}
void insert_move(int *ss,int ele,int clu,double delta){
    int temp = ss[ele];
    ss[ele] = clu;
    CluLen[temp]--;
    CluLen[clu]++;
    ObjClu[temp] -= MatrixNK[ele][temp];
    ObjClu[clu] += MatrixNK[ele][clu];
    updateMatrixNK(ele, temp, clu);
    Objective += delta;
    //Objective= caculateObj(ss);
}
double tbe(int l_iter, int *ss, double maxTime)
{
    LL delta;
    //Objective = caculateObj(ss);
    //one-move move
    int l = 0;
    while ((clock() - StartTime) / CLOCKS_PER_SEC <= maxTime && l < l_iter)
    {
        //打乱顺序，随机构建邻域
        shuffle(randN, randN+N,g);
        shuffle(randK, randK+K,g);
        if (N%K != 0)
        {
            for (int ind = 0; ind < N; ind++)
            {
                int ele = randN[ind];
                for (int jnd = 0; jnd < K; jnd++)
                {
                    int clu = randK[jnd];
                    if (CluLen[ss[ele]] == CluLen[clu] + 1)
                    {
                        delta = cal_insert_delta(ss,ele,clu);
                        if (Objective + delta < ThreshT)
                        {
                            insert_move(ss,ele,clu,delta);
                            if (Objective < ObjBest)
                            {
                                ObjBest = Objective;
                                FinishTime = clock();
                            }
                        }
                    }
                }
            }
        }
        //shuffle(randN,randN+N,g);
        //swap move
        for (int ind = 0; ind < N; ind++)
        {
            int ele = randN[ind];
            for (int ind2 = ind + 1; ind2 < N; ind2++)
            {
                int ele2 = randN[ind2];
                if (ss[ele] != ss[ele2])
                {
                    delta = cal_swap_delta(ss, ele,ele2);
                    if (Objective + delta < ThreshT)
                    {
                        //do swap
                        swap_move(ss,ele,ele2,delta);
                        if (Objective < ObjBest)
                        {
                            ObjBest = Objective;
                            FinishTime = clock();
                        }
                        //checkMove(Objective, ss);
                    }
                }
            }
        }
        //}
        l++;
    }
    return Objective;
}


//descent based improvement
double dbi(int *ss, double maxTime)
{
    LL delta;
    int flag_move = 1;
    //Objective = caculateObj(ss);
    //one-move move
    if (N%K != 0)
    {
        while (flag_move && (clock() - StartTime) / CLOCKS_PER_SEC <= maxTime)
        {
            flag_move = 0;
            //打乱顺序，随机构建邻域
            shuffle(randN, randN+N,g);
            shuffle(randK, randK+K,g);
            for (int ind = 0; ind < N; ind++)
            {
                int ele = randN[ind];
                for (int jnd = 0; jnd < K; jnd++)
                {
                    int clu = randK[jnd];
                    if (CluLen[ss[ele]] == CluLen[clu] + 1)
                    {
                        delta = cal_insert_delta(ss,ele,clu);
                        if (delta < 0)
                        {
                            insert_move(ss,ele,clu,delta);
                            //checkMove(Objective, ss);
                            flag_move = 1;
                        }
                    }
                }
            }
        }
    }
    //swap move
    flag_move = 1;
    while (flag_move && (clock() - StartTime) / CLOCKS_PER_SEC <= maxTime)
    {
        flag_move = 0;
        //打乱顺序，随机构建邻域
        shuffle(randN, randN+N,g);
        for (int ind = 0; ind < N; ind++)
        {
            int ele = randN[ind];
            for (int ind2 = ind + 1; ind2 < N; ind2++)
            {
                int ele2 = randN[ind2];
                if (ss[ele] != ss[ele2])
                {
                    delta = cal_swap_delta(ss,ele,ele2);
                    if (delta < 0)
                    {
                        //shuffle(randN, randN+N,g);
                        //do swap
                        swap_move(ss,ele,ele2,delta);
                        //checkMove(Objective, ss);
                        flag_move = 1;
                        ind=0;
                        ind2=-1;
                    }
                }
            }
        }
    }
    if (Objective < ObjBest)
    {
        ObjBest = Objective;
        FinishTime = clock();
    }
    return Objective;
}

void update_tabu_table(int ele,int clu,int **tabu_table,int iter){
    tabu_table[ele][clu]=iter+1;
}
void makeMove(int *ss,int **tabu_table,int ele1,int ele2,int neighbor_type,LL delta,int iter){
    if(neighbor_type==0){
        int clu=ele2;
        if(clu>=K||clu<0||ele1>=N||ele1<0) cout<<"error"<<endl;
        insert_move(ss,ele1,clu,delta);
        update_tabu_table(ele1,clu,tabu_table,iter);
    }else{
        int clu1=ss[ele1],clu2=ss[ele2];
        //delta= cal_swap_delta(ss,ele1,ele2);
        if(clu1>=K||clu2>=K||clu1<0||clu2<0||ele1<0||ele2<0||ele2>=N||ele1>=N) {
            cout<<ele1<<" "<<ele2<<endl;
            cout<<"error"<<endl;
        }
        swap_move(ss,ele1,ele2,delta);
        update_tabu_table(ele1,clu2,tabu_table,iter);
        update_tabu_table(ele2,clu1,tabu_table,iter);
    }
}

//descent based improvement with tabu
double tabu_dbi(int *ss, double maxTime)
{
    //cout<<"hhhhh"<<endl;

    LL delta;
    int element=-1,cluster=-1;
    int iter=0;
    //邻域类型，0：插入邻域，1：交换邻域
    int tabu_type=-1,non_tabu_type=-1;
    int TABU_MAX_ITER=100;
    int tabu_insert_i=-1,tabu_insert_j=-1,non_tabu_insert_i=-1,non_tabu_insert_j=-1;
    int tabu_swap_i=-1,tabu_swap_j=-1,non_tabu_swap_i=-1,non_tabu_swap_j=-1;
    /*
     * 初始化禁忌表
     */
    int **tabu_table=new int*[N];
    for(int i=0;i<N;i++){
        tabu_table[i]=new int[K];
        for(int j=0;j<K;j++) tabu_table[i][j]=0;
    }
    //Objective = caculateObj(ss);
    //one-move move

    while ((clock() - StartTime) / CLOCKS_PER_SEC <= maxTime && iter < TABU_MAX_ITER)
    {

        iter++;
        LL tabuDelta=MAXNUM,nonTabuDelta=MAXNUM;
        if (N%K != 0) {
            //打乱顺序，随机构建邻域
            shuffle(randN, randN + N, g);
            shuffle(randK, randK + K, g);
            for (int ind = 0; ind < N; ind++) {
                int ele = randN[ind];
                for (int jnd = 0; jnd < K; jnd++) {
                    int clu = randK[jnd];
                    if (CluLen[ss[ele]] == CluLen[clu] + 1) {
                        delta = cal_insert_delta(ss, ele, clu);
                        if (tabu_table[ele][clu] >= iter && delta <= tabuDelta) {
                            //update tabu move
                            tabu_type=0;
                            tabuDelta=delta;
                            tabu_insert_i=ele;
                            tabu_insert_j=clu;
                        } else if (tabu_table[ele][clu] < iter && delta <= nonTabuDelta) {
                            //update nontabu move
                            non_tabu_type=0;
                            nonTabuDelta=delta;
                            non_tabu_insert_i=ele;
                            non_tabu_insert_j=clu;
                        }
                    }
                }
            }
        }

        //打乱顺序，随机构建邻域
        shuffle(randN, randN+N,g);
        for (int ind = 0; ind < N; ind++)
        {
            int ele = randN[ind];
            for (int ind2 = ind + 1; ind2 < N; ind2++)
            {
                int ele2 = randN[ind2];
                if (ss[ele] != ss[ele2])
                {
                    delta = cal_swap_delta(ss,ele,ele2);
                    if(tabu_table[ele][ss[ele2]] >= iter && tabu_table[ele2][ss[ele]] >= iter){
                        if(delta<=tabuDelta){
                            tabu_type=1;
                            tabuDelta=delta;
                            tabu_swap_i=ele;
                            tabu_swap_j=ele2;
                        }
                    }else{
                        //non tabu best move

                        if(delta<=nonTabuDelta){
                            non_tabu_type=1;
                            nonTabuDelta=delta;
                            non_tabu_swap_i=ele;
                            non_tabu_swap_j=ele2;
                        }
                    }
                }
            }
        }

        LL deltaValue;
        int neighbor_type=-1;
        int ele1=-1,ele2=-1;

        //满足禁忌激活条件，可以使用禁忌解
        if(tabuDelta < nonTabuDelta && tabuDelta <0){
            deltaValue=tabuDelta;
            if(tabu_type==0){
                neighbor_type=0;
                ele1=tabu_insert_i;
                ele2=tabu_insert_j;
            }else if(tabu_type==1){
                neighbor_type=1;
                ele1=tabu_swap_i;
                ele2=tabu_swap_j;
            }
        }
        //未能达到禁忌条件，不能使用禁忌解
        else{
            deltaValue=nonTabuDelta;
            if(non_tabu_type==0){
                neighbor_type=0;
                ele1=non_tabu_insert_i;
                ele2=non_tabu_insert_j;
            }else if(non_tabu_type==1){
                neighbor_type=1;
                ele1=non_tabu_swap_i;
                ele2=non_tabu_swap_j;
            }
        }
        makeMove(ss,tabu_table,ele1,ele2,neighbor_type,deltaValue,iter);
    }
    if (Objective < ObjBest)
    {
        ObjBest = Objective;
        FinishTime = clock();
    }
    /*
     * 释放禁忌表占用的空间
     */
    for(int i=0;i<N;i++){
        delete []tabu_table[i];
    }
    //cout<<"hhhhh"<<endl;
    delete []tabu_table;
    return Objective;
}


int rts(int *ss, double maxTime)
{
    int iter = 0, w = 0;
    double currentValue;
    int LL = 5;
    Objective = caculateObj(ss);
    TA = 16.73;                                        //ta,tb,tc 这三个参数怎么确定的
    TB = 76.56;
    TC = 0.0031;

    ObjP = Objective;
    TR = 1 / (TA*(ObjP / 1000) + TB) + TC;
    ThreshT = (1 + TR)*ObjP;
#ifdef __APPLE__
    cout<<ObjP<<" "<<TA<<" "<<TB<<" "<<TC<<" "<<TR<<endl;
    cout << "objective=" << Objective << ",ThreshT=" << ThreshT << endl;
#endif
    initialMatrixNKAndObjClu(ss);
    child_update.cost = MAXNUM;
    //while ((clock() - StartTime) / CLOCKS_PER_SEC <= maxTime)

    while (iter<RTS_ITER)
    {
        currentValue = tbe(LL, ss, maxTime);                                //threshold-based exploration
        currentValue = tabu_dbi(ss, maxTime);                                    //descent-based improvement
        if (currentValue < ObjP)
        {
            ObjP = currentValue;
            FinishTime = clock();
            TR = 1 / (TA*(ObjP / 1000) + TB) + TC;
            ThreshT = (1 + TR)*ObjP;
            w = 0;
        }
        else
            w += 1;
        if (currentValue < child_update.cost)
        {
            child_update.cost = currentValue;
            memcpy(child_update.p, ss, sizeof(int)*N);
        }
        iter++;
    }
    return Objective;
}
/**
 初始化种群
 */
void initialPopulation(double maxTime)
{
    for (int i = 0; i < PopNum; i++)
    {
        if(i<PopNum*RANDOM_POPULATION_RATIO)
            randomConstruction(Pop[i].p);
        else
            greedyConstruction(Pop[i].p);
        initialMatrixNKAndObjClu(Pop[i].p);
        Objective=caculateObj(Pop[i].p);
        dbi(Pop[i].p, 0.01*maxTime);
        Pop[i].cost = Objective;
    }
}

//backbone crossover:基于最大匹配
void crossover()
{
    int parent1, parent2;
    int i, j, m, n;
    int unassLen;
    int ver1, ver2, sharedV, sharedMax;
    int index;
    int can1, can2;
    for (i = 0; i < N; i++)
    {
        Child.p[i] = -1;
        flagV[i] = 0;
    }
    parent1 = better_rand.pick(PopNum);
    parent2 = better_rand.pick(PopNum);
    while (parent1 == parent2)
        parent2 = better_rand.pick(PopNum);
    for (i = 0; i < K; i++)
    {
        len[i] = 0;
        len2[i] = 0;
        flagC1[i] = 0;
        flagC2[i] = 0;
    }
    for (i = 0; i < N; i++)
    {
        int clu = Pop[parent1].p[i];
        arr1[clu][len[clu]++] = i;
        int clu2 = Pop[parent2].p[i];
        arr2[clu2][len2[clu2]++] = i;
    }
    //最大匹配
    sharedMax = 0;

    //循环K次
    for (int iter = 0; iter < K; iter++)
    {
        sharedMax = 0;
        //接下来的两重循环寻找最大匹配的簇
        for (i = 0; i < K; i++)
        {
            //如果这个簇没有被使用过
            if (flagC1[i] == 0)
            {
                for (m = 0; m < K; m++)
                {
                    //如果这个簇没有被使用过
                    if (flagC2[m] == 0)
                    {
                        sharedV = 0;
                        index = 0;
                        for (j = 0; j < len[i]; j++)
                        {
                            ver1 = arr1[i][j];
                            //父点没有被用过
                            if (flagV[ver1] == 0)
                            {
                                for (n = index; n < len2[m]; n++)
                                {
                                    ver2 = arr2[m][n];
                                    //母点没有被用过
                                    if (flagV[ver2] == 0)
                                    {
                                        if (ver1 == ver2)
                                            sharedV++;
                                        if (ver2 > ver1)
                                        {
                                            index = n;
                                            break;
                                        }
                                    }
                                }

                            }
                        }
                        if (sharedV > sharedMax)
                        {
                            sharedMax = sharedV;
                            can1 = i;
                            can2 = m;
                        }
                    }
                }
            }
        }
        match[can1] = can2;
        flagC1[can1] = 1;
        flagC2[can2] = 1;
        /*if (sharedMax > CluLen[iter])
        {
            cout << "please move the cluster to the proper position" << endl;
            getchar();
        }*/
        index = 0;
        for (int x1 = 0; x1 < len[can1]; x1++)
        {
            int ver = arr1[can1][x1];
            for (int x2 = index; x2 < len2[can2]; x2++)
            {
                int ver2 = arr2[can2][x2];
                if (ver == ver2)                    //标记该顶点已被分配到子代
                {
                    flagV[ver] = 1;
                    Child.p[ver] = iter;
                    index = x2;
                    break;
                }
                if (ver2 > ver)
                {
                    break;
                    index = x2;
                }
            }
        }
    }
    for (i = 0; i < K; i++)
        len[i] = 0;
    unassLen = 0;
    for (i = 0; i < N; i++)
    {
        if (Child.p[i] != -1)
        {
            int clu = Child.p[i];
            arr1[clu][len[clu]++] = i;
        }
        else
        {
            unassV[unassLen] = i;
            addressUnaV[i] = unassLen;
            unassLen++;
        }
    }
    //随机分配剩余顶点

    int len111 = 0;
    while (len111 < unassLen)
    {
        int ver = unassV[better_rand.pick(unassLen)];
        int k = better_rand.pick(K);
        while (Child.p[ver] == -1 && len[k] < CluLen[k])
        {
            Child.p[ver] = k;
            len[k]++;
            len111++;
        }
        //cout << "len111=" << len111 <<",unassLen="<<unassLen<< endl;
    }
}

//种群更新：淘汰cost最差的个体,且新生的子代与种群中个体都不一样
void  updatePopulation(int *ch, double cost)
{
    int i, flag_diff;
    double maxCost = -MAXNUM;
    int select;
    for (i = 0; i < PopNum; i++)
    {
        if (Pop[i].cost > maxCost)
        {
            maxCost = Pop[i].cost;
            select = i;
        }
    }
    for (i = 0; i < PopNum; i++) {
        //通过cost的大小简单判断种群是否一样
        if (fabs(Pop[i].cost - cost) < DEVIATION)
            return;
    }
    if (cost < maxCost)
    {
        for (i = 0; i < N; i++)
            Pop[select].p[i] = ch[i];
        Pop[select].cost = cost;
    }
}

//计算两个个体之间的相似度
int Calculate_Sim_Between_Two(int *p1, int *p)
{

    int sum = 0, count, i, sum1, delta;
    int m1, m2, m3, m4, target1, target2;
    memset(flagC1, 0, sizeof(int)*K);
    memset(flagC2, 0, sizeof(int)*K);
    memset(len, 0, sizeof(int)*K);
    memset(len2, 0, sizeof(int)*K);
    for (i = 0; i < N; i++)
    {
        arr1[p1[i]][len[p1[i]]++] = i;
        arr2[p[i]][len2[p[i]]++] = i;
    }
    for (count = 0; count < K; count++)
    {
        delta = 0;
        for (m1 = 0; m1 < K; m1++)
        {

            if (flagC1[m1] != 1)
            {
                for (m2 = 0; m2 < K; m2++)
                {
                    if (flagC2[m2] != 1)                                                                        //表示染色体2 当前色族未被选中
                    {
                        sum1 = 0;
                        for (m3 = 0; m3 <len[m1]; m3++)
                        {
                            for (m4 = 0; m4 <len2[m2]; m4++)
                            {
                                if (arr1[m1][m3] == arr2[m2][m4])
                                {
                                    sum1++;
                                    break;
                                }
                            }

                        }
                        //cout << "sum1=" << sum1 <<" m1="<<m1<<" m2="<<m2<< endl;
                        if (sum1 > delta)                                                //最大匹配
                        {
                            delta = sum1;
                            target1 = m1;
                            target2 = m2;
                        }
                    }

                }
            }
        }
        flagC1[target1] = 1;
        flagC2[target2] = 1;
        sum += delta;
        //diversity = MaxVtx - sum;
        //sumDiversity += diversity;
    }
    return sum;
}

//计算种群相似性
void compute_similarity()
{
    int i, j, sum_sim = 0;
    double similarity;
    for (i = 0; i < PopNum; i++)
        for (j = i + 1; j < PopNum; j++)
            sum_sim += Calculate_Sim_Between_Two(Pop[i].p, Pop[j].p);
    similarity = double(sum_sim) / (N*PopNum*(PopNum - 1) / 2);
#ifdef __APPLE__
    cout << "similarity=" << similarity << endl;
#endif
}

void memetic(double maxTime)
{

    ObjBest = MAXNUM;
    initialPopulation(maxTime);
    int iter = 0;
    while ((clock() - StartTime) / CLOCKS_PER_SEC <= maxTime)
    {
        crossover();
        rts(Child.p, maxTime);
        updatePopulation(child_update.p, child_update.cost);
#ifdef __APPLE__
        printf("generations=%d,objbest=%6f,spend time=%f\n", iter++, (double)ObjBest, (clock() - StartTime) / CLOCKS_PER_SEC);
#endif
    }
    compute_similarity();
}

void freeMemory1()
{
    delete [] CluLen;
    delete [] ObjClu;
    for (int i = 0; i < N; i++)
        delete [] MatrixNK[i];
    delete [] MatrixNK;
    delete [] flagN;
    delete [] flagK;
    delete [] randN;
    delete [] randK;
    for (int i = 0; i < K; i++)
    {
        delete [] arr1[i];
        delete [] arr2[i];
    }
    delete [] arr1;
    delete [] arr2;
    delete [] len;
    delete [] len2;
    delete [] match;
    delete [] flagC1;
    delete [] flagV;
    delete [] unassV;
    delete [] addressUnaV;
}

void freeMemory()
{
    delete [] BestS;
    delete [] Child.p;
    for (int i = 0; i < N; i++)
    {
        delete [] Point[i];
        delete [] DisSquare[i];
    }
    delete [] Point;
    delete [] DisSquare;

}

int main(int argc, char *argv[])
{
    //cout<<<<endl;
    string instances[DATASETNUM];
    //数据集的数据：聚类数目，点数量，点纬度，算例名称
    int nClusters[DATASETNUM];
    int nPoints[DATASETNUM];
    int nDimensions[DATASETNUM];
    string instanceName[DATASETNUM];

    int nCluterK[DATASETNUM][CLUTERNUM];
    int cluK1[CLUTERNUM] = { 2, 3, 4, 6, 7, 10, 11, 13, 15, 20 };
    string PATH;
#ifdef __APPLE__
    PATH = "/Users/dongfengke/CLionProjects/myBmssc/";
#else
    PATH = "C:/Users/dongfengke/source/repos/myBmssc/";

#endif
    //1
    instances[0] = PATH + "datasets/iris.txt";    //150
    nPoints[0] = 150; nDimensions[0] = 4; nClusters[0] = 6;
    instanceName[0] = "iris";
    //2
    instances[1] = PATH + "datasets/wine.txt";    //178
    nPoints[1] = 178; nDimensions[1] = 13; nClusters[1] = 3;
    instanceName[1] = "wine";
    //3
    instances[2] = PATH + "datasets/glass.txt";    //214
    nPoints[2] = 214; nDimensions[2] = 9; nClusters[2] = 7;
    instanceName[2] = "glass";
    //4
    instances[3] = PATH + "datasets/thyroid.txt";//215
    nPoints[3] = 215; nDimensions[3] = 5; nClusters[3] = 3;
    instanceName[3] = "thyroid";
    //5
    instances[4] = PATH + "datasets/ionosphere.txt"; //351
    nPoints[4] = 351; nDimensions[4] = 34; nClusters[4] = 2;
    instanceName[4] = "ionosphere";
    //6
    instances[5] = PATH + "datasets/libra.txt";//360
    nPoints[5] = 360; nDimensions[5] = 90; nClusters[5] = 15;
    instanceName[5] = "libra";
    //7
    instances[6] = PATH + "datasets/user_knowledge.txt";//403
    nPoints[6] = 403; nDimensions[6] = 5; nClusters[6] = 4;
    instanceName[6] = "user_knowledge";
    //8
    instances[7] = PATH + "datasets/body.txt";//507
    nPoints[7] = 507; nDimensions[7] = 5; nClusters[7] = 2;
    instanceName[7] = "body";
    //9
    instances[8] = PATH + "datasets/water.txt";//527
    nPoints[8] = 527; nDimensions[8] = 38; nClusters[8] = 13;
    instanceName[8] = "water";
    //10
    instances[9] = PATH + "datasets/breast.txt";//569
    nPoints[9] = 569; nDimensions[9] = 30; nClusters[9] = 2;
    instanceName[9] = "breast";
    //11
    instances[10] = PATH + "datasets/synthetic.txt";//600
    nPoints[10] = 600; nDimensions[10] = 60; nClusters[10] = 6;
    instanceName[10] = "synthetic";
    //12
    instances[11] = PATH + "datasets/vehicle.txt";//846
    nPoints[11] = 846; nDimensions[11] = 18; nClusters[11] = 6;
    instanceName[11] = "vehicle";
    //13
    instances[12] = PATH + "datasets/vowel.txt";//990
    nPoints[12] = 990; nDimensions[12] = 10; nClusters[12] = 11;
    instanceName[12] = "vowel";
    //14
    instances[13] = PATH + "datasets/yeast.txt"; //1484
    nPoints[13] = 1484; nDimensions[13] = 8; nClusters[13] = 10;
    instanceName[13] = "yeast";
    //15
    instances[14] = PATH + "datasets/multiple.txt";//2000
    nPoints[14] = 2000; nDimensions[14] = 240; nClusters[14] = 7;
    instanceName[14] = "multiple";
    //16
    instances[15] = PATH + "datasets/image.txt";//2310
    nPoints[15] = 2310; nDimensions[15] = 19; nClusters[15] = 7;
    instanceName[15] = "image";
#ifdef __APPLE__
    ofstream resultsFile;
    ofstream valuesFile;
    resultsFile.open(PATH+"resultsFile/resultados_MA_RTS.txt", ofstream::app);
    valuesFile.open(PATH+"valuesFile/solucoes_MA_RTS.txt", ofstream::app);
#endif
    Runs = 10;
    RTS_ITER = 50;
    double bestValue = MAXNUM;
    double avgValue = 0;
    double avgTime = 0;
    double bestTime;
    string timeFile = PATH + "datasets/time1.txt";
    readTimeFile(timeFile);
    ObjBest = MAXNUM;
    /**
     { 2, 3, 4, 6, 7, 10, 11, 13, 15, 20 }
     */
    for (int i = 0; i < DATASETNUM; i++)
        for (int j = 0; j < CLUTERNUM; j++)
            nCluterK[i][j] = cluK1[j];
    for (int i = 1; i < 2; i++)
    {
        N = nPoints[i];
        D = nDimensions[i];
        /**
         将算例中所有点读到Point中
         */
        initialing(instances[i]);
        /**
         循环10种不同的簇
         */
        time_t raw_time;
        struct tm *ptminfo;
        time(&raw_time);
        ptminfo=localtime(&raw_time);
#ifdef __APPLE__
        resultsFile <<ptminfo->tm_year+1900<<"-"<<ptminfo->tm_mon+1<<"-"<<ptminfo->tm_mday<<"-"<<ptminfo->tm_hour<<":"<<ptminfo->tm_min<<":"<<ptminfo->tm_sec<<"   "<<"random/greedy="<<RANDOM_POPULATION_RATIO<<endl;
        valuesFile <<ptminfo->tm_year+1900<<"-"<<ptminfo->tm_mon+1<<"-"<<ptminfo->tm_mday<<"-"<<ptminfo->tm_hour<<":"<<ptminfo->tm_min<<":"<<ptminfo->tm_sec<<"   "<<"random/greedy="<<RANDOM_POPULATION_RATIO<<endl;
#endif
        for (int k = 0; k < CLUTERNUM; k++)
        {
            K = nCluterK[i][k];
            allocateMemory();
            //buildNeighbors();
            bestValue = MAXNUM;
            bestTime = MAXNUM;
            avgValue = 0;
            avgTime = 0;
#ifdef __APPLE__
            cout << "=================================================INSTANCE " << i + 1 << "=================================================" << endl;
            cout << "Location: " << instances[i] << endl;
            cout << "Clusters: " << K << endl;
            valuesFile << instanceName[i] << ":";
#endif
            for (int j = 0; j < Runs; j++)
            {
#ifdef __APPLE__
                cout << "------------------------------------- Execution " << j + 1 << "-----------------------------------------" << endl;
                cout << "maxTime = " << MaxTimes[i][k][j] << endl;
#endif
                StartTime = clock();
                memetic(MaxTimes[i][k][j]);
                Runtime = (FinishTime - StartTime) / CLOCKS_PER_SEC;
#ifdef __APPLE__
                cout << endl << setprecision(6) << scientific << "Objective Function value: " << ObjBest << " in " << setprecision(2) << fixed << Runtime << " seconds" << endl;
#endif
                if (ObjBest < bestValue)
                    bestValue = ObjBest;
                if (Runtime < bestTime)
                    bestTime = Runtime;
                avgValue += ObjBest;
                avgTime += Runtime;
#ifdef __APPLE__
                valuesFile << setprecision(6) << scientific << ObjBest << ";";
#endif
            }
#ifdef __APPLE__
            resultsFile << instanceName[i] << ":bestV=" << setprecision(6) << scientific << bestValue;
            resultsFile << ",avgV=" << setprecision(6) << scientific << avgValue / Runs;
            resultsFile << ",bestTime=" << setprecision(2) << fixed << bestTime;
            resultsFile << ",avgTime=" << setprecision(2) << fixed << avgTime / Runs << ",K=" << K << endl;
            valuesFile << ",K=" << K << endl;
#endif
            cout << endl;
            freeMemory1();
        }
        freeMemory();
    }
}
