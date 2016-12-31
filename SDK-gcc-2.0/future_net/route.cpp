#include "lib_io.h"
#include "lib_time.h"
#include "lib_record.h"
#include "route.h"
#include <time.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <queue>
#include <stack>

#include <iostream>
#include <algorithm>

using namespace std;

#define ILLEGAL 2
#define DEMAND 2
#define MAX_NODE 2005
#define MAX_CITY 105
#define INF_DIS 20000000.0
#define TOPK 10//定义10个关键节点
//#define TSP_LIMIT 50
//#define ADD_WEIGHT 30000


#define PROB 0.3
int ADD_WEIGHT;
int TSP_LIMIT = 50;
int IT_COUNT;
int unit_num;//群体规模
int FLAG_DATA;
typedef struct
{
    int u;
    int v;
    int index;//边标号
    double weight;//权值
    int next;//下一条边
    bool is_add;
} OriginEdge;
typedef struct
{
    double weight;
    int *path;
    int path_num;
    int *path_node;
} CompMat;

//void add_neareset(int demand_k);

int TopK[DEMAND][MAX_NODE];//每个点的统计
int topk[DEMAND];//统计最多的
bool LEVEL_UP;
bool NA_FLAG[DEMAND];
int repeat[MAX_NODE*20];//重复边

vector<int>repeat_vector;//repeat edge index
vector<int>be_add_vector;// add paths

struct Best_ans
{
    vector<int>best_path[DEMAND];
    int repeat_edge;
    int weight;
    void best_ans_init();
};
void Best_ans::best_ans_init()
{
    best_path[0].clear();
    best_path[1].clear();
    repeat_edge = MAX_NODE*20;
    weight = INF_DIS;
}
vector<int>ans_vector[DEMAND];
Best_ans best_ans;
int add_cnt;
int best_weight;


typedef pair<int, int>pii;//pair 先比较第一维，再比较第二维
OriginEdge origin_edge[MAX_NODE*20];
int preOrign[MAX_NODE*20];
int node_num;//总的点数目
int city_num[DEMAND];//城市数目
int no_city_num;
int begin_city[DEMAND];//开始城市
int end_city[DEMAND];//结束城市
int ind[MAX_NODE];//入度
bool hash_node[DEMAND][MAX_NODE];//判断是否是关键节点，和非关键节点。
int hash_city[DEMAND][MAX_CITY];
int city_hash[DEMAND][MAX_NODE];//
int edge_hash[MAX_NODE*20];//边的hash
int city_index[MAX_CITY];//
CompMat matrix_city[DEMAND][MAX_CITY][MAX_CITY];//tsp城市

int dist[MAX_NODE];
int path_num[MAX_NODE];
int pre[MAX_NODE];
bool S[MAX_NODE];
int ok[MAX_NODE];

typedef pair<int, int>pii;//pair 先比较第一维，再比较第二维

void init_matrix()
{
    memset(hash_node[0], false, sizeof(hash_node[0]));
    memset(hash_node[1], false, sizeof(hash_node[1]));
    memset(city_hash, -1, sizeof(city_hash));
    memset(edge_hash, -1, sizeof(edge_hash));
    node_num = 0;
    for(int k = 0; k < DEMAND; k++)
    {
        city_num[k] = 0;
    }
}

void build_city(char** demand, int k)
{
	NA_FLAG[k] = 0;
    int cnt = 0;
    int tmp;
    int demand_length = strlen(demand[k]);
    for(int i = 0; i < demand_length; i++)
        if(demand[k][i] == '|')
            cnt++;
    sscanf(demand[k],"%d,%d,%d,%s", &tmp, &begin_city[k], &end_city[k], demand[k]);

    hash_node[k][begin_city[k]] = false;//起点为城市
    hash_node[k][end_city[k]] = false;//终点为城市

    hash_city[k][0] = begin_city[k];//第0个为没有映射过的起点坐标。
    city_hash[k][begin_city[k]] = 0;//记录为第几个关键城市
    hash_city[k][1] = end_city[k];//第1个为没有映射过的终点坐标
    city_hash[k][end_city[k]] = 1;//记录为终点标号为1
    if(cnt == 0)
    {
		city_num[k] = 2;
		NA_FLAG[k] = 1;
        return;
    }

    for(int i = 0; i < cnt; i++)
    {
        sscanf(demand[k], "%d|%s",&city_index[i],demand[k]);
        city_hash[k][city_index[i]] = i+2;//映射坐标从2开始
        hash_node[k][city_index[i]] = false;// 为关键节点
    }
    sscanf(demand[k], "%d", &city_index[cnt]);
    city_hash[k][city_index[cnt]] = cnt+2;
    hash_node[k][city_index[cnt]] = false;
    city_num[k] = cnt+1+2;
    for(int i = 2; i < city_num[k]; i++)
    {
        hash_city[k][i] = city_index[i-2];
    }
}

void build_graph(char **topo, int edge_num, char **demand, int demand_num)
{
    int u, v, edge_index;
    double weight;
    memset(preOrign, -1, sizeof(preOrign));
    for(int i = 0; i < edge_num; i++)
    {
        sscanf(topo[i],"%d,%d,%d,%lf",&edge_index,&u,&v,&weight);
        origin_edge[i].u = u;
        origin_edge[i].v = v;
        origin_edge[i].weight = weight;
        origin_edge[i].index = edge_index;
        origin_edge[i].is_add = false;
        edge_hash[edge_index] = i;
        origin_edge[i].next = preOrign[u];
        preOrign[u] = i;
        if(!hash_node[0][u])
        {
            hash_node[0][u] = true;
            node_num++;
        }
        if(!hash_node[1][u])
        {
            hash_node[1][u] = true;
        }
        if(!hash_node[0][v])
        {
            hash_node[0][v] = true;
            node_num++;
        }
        if(!hash_node[1][v])
        {
            hash_node[1][v] = true;
        }
    }
    cout<<"node_num == "<<node_num<<endl;
    if(node_num > 1300)
    {
        IT_COUNT = 100000;
        FLAG_DATA = 3;
        unit_num = 1;
    }
    else if(node_num > 500)
    {
        IT_COUNT = 50000;
        FLAG_DATA = 2;
        unit_num = 5;
    }
    else if(node_num > 100)
    {
        IT_COUNT = 10000;
        FLAG_DATA = 1;
        unit_num = 20;
    }
    else
    {
        IT_COUNT = 4000;
        FLAG_DATA = 0;
        unit_num = 20;
    }
}

void record_path(int k, const int& x, const int& from, const int& to, const pii& u)
{
    int path_cnt = path_num[x];
    int path_temp[path_cnt];
    int path_node[path_cnt+1];
    int cur_point = x;//当前点
    int edge_number = pre[cur_point];//当前点之前的边是edge number;
    for(int i = path_cnt -1; i >= 0; i--)
    {
        int ss = origin_edge[edge_number].u;
        path_temp[i] = origin_edge[edge_number].index;
        path_node[i] = ss;
        edge_number = pre[ss];//到上个点之前的变。
    }
    int *path = (int *)malloc(path_cnt*sizeof(int));
    for(int i = 0; i < path_cnt; i++)//记录路径
        path[i] = path_temp[i];
    int *node = (int *)malloc((path_cnt - 1)*sizeof(int));
    for(int i = 0; i < path_cnt -1; i++)//把经过的点记录下来
        node[i] = path_node[i+1];
    matrix_city[k][city_hash[k][from]][city_hash[k][x]].path = path;
    matrix_city[k][city_hash[k][from]][city_hash[k][x]].path_num = path_cnt;
    matrix_city[k][city_hash[k][from]][city_hash[k][x]].path_node = node;
    matrix_city[k][city_hash[k][from]][city_hash[k][x]].weight = u.first;//路径长度记录了。
}

void dijkstra_link(const int k, const int &from, const int& to, int *ok)
{
    for(int i = 0; i < MAX_NODE; i++)
        dist[i] = INF_DIS;
    memset(pre, -1, sizeof(pre));
    memset(path_num, 0, sizeof(path_num));
    memset(S, false, sizeof(S));
//    for(int i = 0; i < MAX_NODE; i++)//这个循环是用来判断在用dij的时候，哪些点被排除在外了。
//    {
//        if(ok[i] != 1)
//        {
//            S[i] = true;
//        }
//    }
    if(from != begin_city[k])
    {
        S[begin_city[k]] = true;
    }

    priority_queue<pii,vector<pii>,greater<pii>> q;
    dist[from] = 0;
    q.push(make_pair(dist[from], from));
    while(!q.empty())
    {
        pii u = q.top();
        q.pop();
        int x = u.second;
        if(S[x])
            continue;
        S[x] = true;
        if(hash_node[k][x] == false && x != from)//关键节点，非起点的关键节点
        {
            ok[x] = 0;
            if(to != -1 && x == to)//记录从 from 到 to之间路径。
            {
                record_path(k, x, from, to, u);
                return ;
            }
            else if(to == -1)//记录全部路径//全部降解
            {
                record_path(k, x, from, to, u);
            }
        }
        if(ok[x] == 1)
        {
            for(int e = preOrign[x]; e != -1; e = origin_edge[e].next)
            {
                if(dist[origin_edge[e].v] > dist[x] + origin_edge[e].weight)
                {
                    dist[origin_edge[e].v] = dist[x] + origin_edge[e].weight;
                    pre[origin_edge[e].v] = e;//记录这点之前的这条边标号
                    path_num[origin_edge[e].v] = path_num[x] + 1;//
                    q.push(make_pair(dist[origin_edge[e].v], origin_edge[e].v));
                }
            }
        }
    }
}

void compress_start_end(int k)
{
    matrix_city[k][1][0].weight = 0.0005;//终点到起点
    matrix_city[k][1][0].path = NULL;
    matrix_city[k][1][0].path_node = NULL;
    matrix_city[k][1][0].path_num = 0;
}

void compress_graph_init(const int& demand_k)
{
    for(int i = 0; i < city_num[demand_k]; i++)
    {
        for(int j = 0; j < city_num[demand_k]; j++)
        {
            matrix_city[demand_k][i][j].weight = INF_DIS;
            matrix_city[demand_k][i][j].path_node = NULL;
            matrix_city[demand_k][i][j].path_num = 0;
            matrix_city[demand_k][i][j].path = NULL;
        }
    }
}

void compress_graph(int k)
{
    compress_graph_init(k);
    for(int i = 0; i < city_num[k]; i++)
    {
        if(i == 1)//如果是终点，则终点和其他店距离都为无穷大，不需要计算。
            continue;
        for(int j = 0; j < MAX_NODE; j++ )ok[j] = 1;
        dijkstra_link(k, hash_city[k][i], -1, ok);
    }
    compress_start_end(k);
}

void statistics_num(int k)
{
    memset(TopK, 0, sizeof(TopK));//全部赋值为0统计之前
    memset(topk, 0, sizeof(topk));//设为0
    for(int i = 0; i < city_num[k]; i++)
    {
        for(int j = 0; j < city_num[k]; j++)
        {
            for(int x = 0; x < matrix_city[k][i][j].path_num-1; x++)
            {
                TopK[k][matrix_city[k][i][j].path_node[x]]++;
            }
        }
    }
    int index = 0;
    for(int i = 0; i < MAX_NODE; i++)
    {
        if(TopK[k][i] > topk[k])
        {
            topk[k] = TopK[k][i];
            index = i;
        }
    }
    topk[k] = index;//设置下标
}


void add_city(int k)//把非关键节点加到关键节点上去
{
    //sscanf(demand[k], "%d", &city_index[cnt]);
    int cnt = city_num[k];
    city_index[cnt-2] = topk[k];
    printf("---------------------kkkk === %d\n",topk[k]);
    city_hash[k][city_index[cnt-2]] = cnt;
    hash_node[k][city_index[cnt-2]] = false;
    city_num[k] = cnt+1;
    hash_city[k][city_num[k]-1] = city_index[cnt-2];

}
void free_all(int k)
{
    for(int i = 0; i < city_num[k]; i++)
    {
        for(int j = 0; j < city_num[k]; j++)
        {
            free(matrix_city[k][i][j].path);
            free(matrix_city[k][i][j].path_node);
            matrix_city[k][i][j].path_num = 0;
            matrix_city[k][i][j].weight = INF_DIS;
        }
    }

}
void level_up(int k)
{
    statistics_num(k);
    add_city(k);
    free_all(k);
    compress_graph(k);
}


void free_from_to(const int& demand_k, const int& u, const int& v)
{
    //free(matrix_city[demand_k][u][v].path);// = NULL;
    //free(matrix_city[demand_k][u][v].path_node);
    matrix_city[demand_k][u][v].path_num = 0;
    matrix_city[demand_k][u][v].weight = INF_DIS;

}
bool ans_legal(const int& demand_k, int from, int to, int *ok, int *ind)
{
    for(int j = 0; j < matrix_city[demand_k][from][to].path_num-1; j++)
    {
        ind[matrix_city[demand_k][from][to].path_node[j]]++;
        if(ind[matrix_city[demand_k][from][to].path_node[j]] == ILLEGAL)
        {
            ok[hash_city[demand_k][from]]++;
            ok[hash_city[demand_k][to]]++;
            for(int n = 0; n < matrix_city[demand_k][from][to].path_num-1; n++)
            {
                //output_matrix_info();
                //printf("%d ",)
                ok[matrix_city[demand_k][from][to].path_node[n]]++;
                //printf("%d ",ok[matrix_city[from][to].path_node[n]]);
            }
            free_from_to(demand_k, from, to);
            dijkstra_link(demand_k, hash_city[demand_k][from], hash_city[demand_k][to], ok);
            return false;
        }
    }
    return true;
}


void add_weight(const int& edge_index)
{
    origin_edge[edge_hash[edge_index]].is_add = true;
    origin_edge[edge_hash[edge_index]].weight = origin_edge[edge_hash[edge_index]].weight + ADD_WEIGHT;
    be_add_vector.push_back(edge_index);
}
void sub_weight(const int edge_index)
{
    if(origin_edge[edge_hash[edge_index]].is_add == true)
    {
        origin_edge[edge_hash[edge_index]].weight -= ADD_WEIGHT;
        origin_edge[edge_hash[edge_index]].is_add = false;
    }
}

const int genmax = 600000;//最大迭代数
int ps = 100;//变异概率

struct Unit
{
public:
    int path[MAX_CITY];//个体的路径信息
    double length;//个体价值
    int flag[MAX_CITY];//每个城市的位置映射
    bool operator < (const Unit& t) const
    {
        return length < t.length;
    }
};

struct Best_Unit
{
    double length;
    int *path;
    int *flag;
};
Best_Unit best;

#define RAND(k) (rand()%(city_num[k]-2)+2)

class Group
{
public:
    Unit group[102];
    Best_Unit best;//最优个体
    int best_gen;//最优个体所出现的迭代数
    int k;//跟遗传本身无关，判断求第一条还是第二条路径
    int len;
    int slide;

    Group(){}

    void init(int _k)
    {
        k = _k;

        slide = city_num[k]/4+1;

        best.length = INF_DIS*100;
        best_gen = 0;
        len = city_num[k]-2;

        for(int i = 0; i < unit_num; i++)
        {
            memset(group[i].flag, -1, sizeof(group[i].flag));

            group[i].path[len] = 1;
            group[i].path[len+1] = 0;
            group[i].flag[1] = len;
            group[i].flag[0] = len+1;

            for(int j = 0; j < len; j++)
            {
                int t_city = RAND(k);
                while(group[i].flag[t_city] != -1)
                    t_city = RAND(k);
                group[i].flag[t_city] = j;
                group[i].path[j] = t_city;
            }

            group[i].length = matrix_city[k][0][group[i].path[0]].weight
                            + matrix_city[k][group[i].path[len-1]][1].weight;

            for(int j = 1; j < len; j++)
                group[i].length += matrix_city[k][group[i].path[j-1]][group[i].path[j]].weight;
        }
    }

    void update()
    {
        best_gen = 0;
        for(int i = 0; i < unit_num; i++)
        {
            group[i].length = matrix_city[k][0][group[i].path[0]].weight
                            + matrix_city[k][group[i].path[len-1]][1].weight;
            for(int j = 1; j < len; j++)
                group[i].length += matrix_city[k][group[i].path[j-1]][group[i].path[j]].weight;
        }

        best.length = matrix_city[k][0][best.path[0]].weight
                            + matrix_city[k][best.path[len-1]][1].weight;
        for(int j = 1; j < len; j++)
            best.length += matrix_city[k][best.path[j-1]][best.path[j]].weight;
    }

    //根据评估结果对个体进行排序
    void unit_sort()
    {
       sort(group, group+unit_num);
    }

    int get_left(int x)
    {
        return (x-1+(city_num[k]))%(city_num[k]);
    }

    int get_right(int x)
    {
        return (x+1)%(city_num[k]);
    }

    Unit cross_nj(const Unit &father, const Unit &mother)
    {
        int c = RAND(k);
        int t = mother.path[ get_left(mother.flag[ father.path[c] ]) ];
        t = father.flag[t];

        Unit sonl, sonr;
        memcpy(&sonl, &father, sizeof(Unit));
        memcpy(&sonr, &father, sizeof(Unit));

        int l = get_left(c);
        sonl.length -= matrix_city[k][ father.path[get_left(l)] ][ father.path[l] ].weight;
        sonl.length -= matrix_city[k][ father.path[l] ][ father.path[get_right(l)] ].weight;
        sonl.length -= matrix_city[k][ father.path[get_left(t)] ][ father.path[t] ].weight;
        sonl.length -= matrix_city[k][ father.path[t] ][ father.path[get_right(t)] ].weight;
        swap(sonl.path[l], sonl.path[t]);
        sonl.flag[ sonl.path[l] ] = t;
        sonl.flag[ sonl.path[t] ] = l;
        sonl.length += matrix_city[k][ father.path[get_left(l)] ][ father.path[t] ].weight;
        sonl.length += matrix_city[k][ father.path[t] ][ father.path[get_right(l)] ].weight;
        sonl.length += matrix_city[k][ father.path[get_left(t)] ][ father.path[l] ].weight;
        sonl.length += matrix_city[k][ father.path[l] ][ father.path[get_right(t)] ].weight;

        int r = get_right(c);
        sonr.length -= matrix_city[k][ father.path[get_left(r)] ][ father.path[r] ].weight;
        sonr.length -= matrix_city[k][ father.path[r] ][ father.path[get_right(r)] ].weight;
        sonr.length -= matrix_city[k][ father.path[get_left(t)] ][ father.path[t] ].weight;
        sonr.length -= matrix_city[k][ father.path[t] ][ father.path[get_right(t)] ].weight;
        swap(sonr.path[r], sonr.path[t]);
        sonr.flag[ sonr.path[r] ] = t;
        sonr.flag[ sonr.path[t] ] = r;
        sonr.length += matrix_city[k][ father.path[get_left(r)] ][ father.path[t] ].weight;
        sonr.length += matrix_city[k][ father.path[t] ][ father.path[get_right(r)] ].weight;
        sonr.length += matrix_city[k][ father.path[get_left(t)] ][ father.path[r] ].weight;
        sonr.length += matrix_city[k][ father.path[r] ][ father.path[get_right(t)] ].weight;

        if(sonl.length < sonr.length)
        {
            if(sonl.length > father.length)
                return father;
            else
                return sonl;
        }
        else
        {
            if(sonr.length > father.length)
                return father;
            else
                return sonr;
        }
    }

    void variation(Unit &p)//变异
    {
        // int a = rand()%(len-slide);
        // int b = a + slide;

        int a = rand()%len;
        int b = rand()%len;
        while(abs(a-b) >= slide)
        {
            a = rand()%len;
            b = rand()%len;
        }

        if(a > b)
            swap(a, b);

        if(b == len-1)
            return;

        int c = rand()%len;
        while(c <= b)
            c = rand()%len;

        Unit it;
        memcpy(&it, &p, sizeof(Unit));
//      cout<<"-=-=  "<<it.length<<endl;
        //减去a左面的路径
        it.length -= matrix_city[k][ it.path[get_left(a)] ][ it.path[a] ].weight;
        //减去b右面的路径
        it.length -= matrix_city[k][ it.path[b] ][ it.path[get_right(b)] ].weight;
        //减去c右面的路径
        it.length -= matrix_city[k][ it.path[c] ][ it.path[get_right(c)] ].weight;
        //加上c到a的路径
        it.length += matrix_city[k][ it.path[c] ][ it.path[a] ].weight;
        //加上b到c右面的路径
        it.length += matrix_city[k][ it.path[b] ][ it.path[get_right(c)] ].weight;
        //加上a左面到b右面的路径
        it.length += matrix_city[k][ it.path[get_left(a)] ][ it.path[get_right(b)] ].weight;
  //    cout<<"+=+=  "<<it.length<<endl;

  //    cout<<it.path[get_left(a)]<<" -- "<<it.path[a]<<endl;
  //    cout<<it.path[b]<<" -- "<<it.path[get_right(b)]<<endl;
  //    cout<<it.path[c]<<" -- "<<it.path[get_right(c)]<<endl;

        // cout<<it.path[c]<<" -- "<<it.path[a]<<endl;
  //    cout<<it.path[b]<<" -- "<<it.path[get_right(c)]<<endl;
  //    cout<<it.path[get_left(a)]<<" -- "<<it.path[get_right(c)]<<endl;


        int temp[MAX_CITY];
        int pos = 0;
        // cout<<a<<"=="<<b<<"=="<<c<<endl;
        for(int i = 0; i < a; i++)
            temp[pos++] = it.path[i];
        for(int i = b+1; i < c; i++)
            temp[pos++] = it.path[i];
        temp[pos++] = it.path[c];
        for(int i = a; i <= b; i++)
            temp[pos++] = it.path[i];

        // for(int i = 0; i < len+2; i++)
        //  printf("%d ", it.path[i]);
        // puts("");
        //cout<<pos<<endl;
        for(int i = 0; i < pos; i++)
            it.path[i] = temp[i];

        // for(int i = 0; i < len+2; i++)
        //  printf("%d ", it.path[i]);
        // puts("");

        if(it.length < p.length)
            memcpy(&p, &it, sizeof(Unit));
    }

    //输出信息
    void print()
    {
        for(int i = 0; i < unit_num; i++)
        {
            printf("第%d个个体，路径信息： 0 ", i);

            for(int j = 0; j < len; j++)
                printf("%d ", group[i].path[j]);

            printf("1 ;总权值：%lf;\n", group[i].length);
        }
        printf("最优个体，路径信息： 0 ");
        for(int j = 0; j < len; j++)
            printf("%d ", group[0].path[j]);

        printf("1 ;总权值：%lf;\n", group[0].length);
    }

    void work()
    {
        for(int i = 0; i < genmax; i++)
        {
            if(unit_num != 1)
                unit_sort();//根据评估结果排序
            //print();
            if(best.length > group[0].length)
            {
                best.length = group[0].length;
                best.flag = group[0].flag;
                best.path = group[0].path;
                //memcpy(&best, &group[0], sizeof(group[0]));
                best_gen = i;
            }

            for(int j = unit_num-1; j >= 0; j--)
            {
//                if(unit_num != 1)
//                {
//                    int t = rand()%unit_num;
//                    while(t == j)
//                        t = rand()%unit_num;
//                    group[j] = cross_nj(group[j], group[t]);
//                }
                variation(group[j]);
            }
            //getchar();
            if(i - best_gen > IT_COUNT)
                break;
        }
    }
};


bool handle_conflicts_plan_2(const int& demand_k, vector<int>&path_nodes)
{
    for(int i = 0; i < MAX_NODE; i++)ok[i] = 1;
    memset(ind, 0, sizeof(ind));
    int from, to;
    for(int i = 0; i < city_num[demand_k]; i++)
    {
        //int from = tsp.best_ant.path_node[i];
        from = path_nodes[i];
        //int to = tsp.best_ant.path_node[(i+1)%(city_num[demand_k])];
        to = path_nodes[(i+1)%(city_num[demand_k])];
//        puts("hash_val");
//        printf("%d ", from);
        ok[hash_city[demand_k][from]]--;
        for(int j = 0; j < matrix_city[demand_k][from][to].path_num-1; j++)
        {
            ok[matrix_city[demand_k][from][to].path_node[j]]--;
        }
    }
    for(int i = 0; i < city_num[demand_k]; i++)
    {
        //from = tsp.best_ant.path_node[i];
        from = path_nodes[i];
        //to = tsp.best_ant.path_node[(i+1)%(city_num[demand_k])];
        to = path_nodes[(i+1)%city_num[demand_k]];
        if(!ans_legal(demand_k,from, to, ok, ind))
        {
            return true;
        }
    }
    return false;
}
/******************/

struct ConflictElem
{
    int edge_index;//第几条边;1 - 2 - 3 - 4 - 1;总共有5条边，
    int conflict_number;
    vector<int> conflict_node;
    ConflictElem()
    {
        this->edge_index = -1;
        this->conflict_number = 0;
        this->conflict_node.resize(0);
    }
};
struct ConflictCmp
{
    bool operator()(ConflictElem *a, ConflictElem *b)
    {
        return a->conflict_number < b->conflict_number;
    }
};

priority_queue<ConflictElem*, vector<ConflictElem*>, ConflictCmp> conflict_heap;

void update_heap(int demand_k, ConflictElem *current_ptr,  vector<ConflictElem*>&conflict_ptr, vector<ConflictElem*>&conflicts_copy, vector<vector<int>>&conflict_nodes_path)
{
    vector<int>&nodes = current_ptr->conflict_node;
    int edge_index;
    for(int i = 0; i < nodes.size(); i++)
    {
        vector<int>& edge_vector = conflict_nodes_path[nodes[i]];///第i个点对应的有冲突的边。
        for(int j = 0; j < edge_vector.size(); j++)
        {
            edge_index = edge_vector[j];///有冲突的边编号。
            conflicts_copy[edge_index]->conflict_number--;
        }
    }
}


bool re_compress(const int& demand_k, vector<int>&path_node, vector<ConflictElem*>&conflicts_ptr, vector<ConflictElem*>&conflicts_copy, vector<vector<int>>&conflict_nodes_path, int *ok)
{
    ConflictElem *current_ptr = conflict_heap.top();
    if(current_ptr->conflict_number == 0)
        return false;///不用降解
    bool rec_flag = false;
    while(!conflict_heap.empty())
    {
        current_ptr = conflict_heap.top();
        conflict_heap.pop();
        if(current_ptr->conflict_number == 0)//降解完毕了。
            break;
        if(current_ptr->conflict_number <= 2)
        {
            rec_flag = true;
            break;///如果最大的冲突数小于等于2，不再进行降解
        }
        int edge_tmp = current_ptr->edge_index;
        int from = path_node[edge_tmp];
        int to = path_node[edge_tmp+1];
        ok[hash_city[demand_k][from]] = 1;///這条边的起点终点开始设置为可以访问
        ok[hash_city[demand_k][to]] = 1;
        for(int i = 0; i < matrix_city[demand_k][from][to].path_num-1; i++)
            ok[matrix_city[demand_k][from][to].path_node[i]] = 1;///这两点之见的非必经点不能访问。
        for(int i = 0; i < current_ptr->conflict_node.size(); i++)///冲突的点不能访问
            ok[current_ptr->conflict_node[i]] = 0;
        free_from_to(demand_k, from, to);///释放这两点，
        dijkstra_link(demand_k, hash_city[demand_k][from], hash_city[demand_k][to], ok);///重新降解这两点
        //update_heap(demand_k, current_ptr, conflicts_ptr, conflicts_copy, conflict_nodes_path);///更该堆
        update_heap(demand_k, current_ptr, conflicts_ptr, conflicts_copy, conflict_nodes_path);

        ok[hash_city[demand_k][from]] = 0;///這条边的起点终点开始设置为可以访问
        ok[hash_city[demand_k][to]] = 0;
        for(int i = 0; i < matrix_city[demand_k][from][to].path_num-1; i++)
            ok[matrix_city[demand_k][from][to].path_node[i]] = 0;
       while(!conflict_heap.empty())
           conflict_heap.pop();
       for(int i = 0; i < city_num[demand_k]-1; i++)
           conflict_heap.push(conflicts_ptr[i]);
    }
    if(rec_flag)
    {
        int edge_tmp = current_ptr->edge_index;
        int from = path_node[edge_tmp];
        int to = path_node[edge_tmp+1];
        ok[hash_city[demand_k][from]] = 1;///這条边的起点终点开始设置为可以访问
        ok[hash_city[demand_k][to]] = 1;
        for(int i = 0; i < matrix_city[demand_k][from][to].path_num-1; i++)
            ok[matrix_city[demand_k][from][to].path_node[i]] = 1;///这两点之见的非必经点不能访问。
       for(int i = 0; i < current_ptr->conflict_node.size(); i++)///冲突的点不能访问
            ok[current_ptr->conflict_node[i]] = 0;
        free_from_to(demand_k, from, to);
        dijkstra_link(demand_k, hash_city[demand_k][from], hash_city[demand_k][to], ok);///重新降解这两点
        //add_neareset(demand_k);
        ok[hash_city[demand_k][from]] = 0;///這条边的起点终点开始设置为可以访问
        ok[hash_city[demand_k][to]] = 0;
        for(int i = 0; i < matrix_city[demand_k][from][to].path_num-1; i++)
            ok[matrix_city[demand_k][from][to].path_node[i]] = 0;
    }
    return true;
}
void handle_conflicts(const int& demand_k, ConflictElem* conflicts_elem, vector<int>&conflicts_node, vector<vector<int>>&conflicts_nodes_path)
{
    //int total_conflicts = 0;

    // 冲突边元素只有城市那么多个。-1个
    for(int i = 0; i < conflicts_node.size(); i++)///这些是冲突的点
    {
        int node = conflicts_node[i];
        for(int j = 0; j < conflicts_nodes_path[node].size(); j++)
        {
            int edge_index = conflicts_nodes_path[node][j];///这些点记录着哪些边冲突了。
            conflicts_elem[edge_index].conflict_number += conflicts_nodes_path[node].size()-1;///当前的进行冲突加
            conflicts_elem[edge_index].conflict_node.push_back(node);
            conflicts_elem[edge_index].edge_index = edge_index;
            //conf_elem[edge_index].conflict_node.push_back(node);///对冲突点进行push
        }
    }
}
bool remove_conflicts(const int& demand_k, vector<int>& path_node, int* ok)//ok数组用于确认是否在该图里
{


    vector<vector<int>>conflict_nodes_path(MAX_NODE);///记录几号点有冲突，并记录该点冲突边是多少。
    vector<int>conflicts_node;/// 这个是记录有冲突的点。

    ConflictElem conf_elem[city_num[demand_k]-1];/// 冲突的元素，第几条边冲突，冲突的次数，冲突的点是什么

    vector<ConflictElem*>conflicts_ptr;///指针
    vector<ConflictElem*>conflicts_copy;///副本
    conflicts_ptr.resize(city_num[demand_k]-1);///设置大小
    conflicts_copy.resize(city_num[demand_k]-1);
    for(int i = 0; i < city_num[demand_k]-1; i++){///赋值
        conflicts_ptr[i] = &conf_elem[i];
        conflicts_copy[i] = &conf_elem[i];
    }
    for(int i = 0; i < city_num[demand_k]-1; i++)///
    {
        int from = path_node[i];
        int to = path_node[i+1];
        ok[hash_city[demand_k][from]]--;//屏蔽关键点
        for(int j = 0; j < matrix_city[demand_k][from][to].path_num - 1; j++)
        {
            ok[matrix_city[demand_k][from][to].path_node[j]]--;///先把所有的点频闭了
            vector<int>& temp = conflict_nodes_path[matrix_city[demand_k][from][to].path_node[j]];
            temp.push_back(i);
            if(temp.size() == 2)
            {
                conflicts_node.push_back(matrix_city[demand_k][from][to].path_node[j]);
            }
        }
    }
    ok[hash_city[demand_k][path_node[demand_k]-1]]--;///把最后一个关键点也屏蔽了。
    //printf("%d \n",hash_city[demand_k][path_node[city_num[demand_k]-1]]);
    //system("pause");
    while(!conflict_heap.empty())
        conflict_heap.pop();
    handle_conflicts(demand_k, conf_elem, conflicts_node, conflict_nodes_path);

    for(int i = 0; i < city_num[demand_k]-1; i++)///把conflicts_指针加入堆
        conflict_heap.push(conflicts_ptr[i]);
    bool flag = re_compress(demand_k, path_node, conflicts_ptr, conflicts_copy, conflict_nodes_path, ok);
    if(flag)//如果有重新降解
    {
        return true;
    }
    else
    {
        return false;//如果没有重新降解
    }
}

/******************/

bool tsp_solve(const int& demand_k, Group& g)
{
    int ok[MAX_NODE];
    memset(ind, 0, sizeof(ind));
    for(int i = 0; i < MAX_NODE; i++)ok[i] = 1;
    if(NA_FLAG[demand_k])
	{
		g.best.length = matrix_city[demand_k][0][1].weight;
		g.best.path = (int*)malloc(sizeof(int)*4);
		g.best.path[0] = 1;
		g.best.path[1] = 0;
	}
	else
	{
		g.work();
	}
    vector<int>path_nodes;///用来存tsp路径顺序
    path_nodes.clear();
    path_nodes.resize(city_num[demand_k]);
    path_nodes[0] = 0;
    for(int i = 0; i < path_nodes.size()-1; i++)
        path_nodes[i+1] = g.best.path[i];
    cout<<"demand_k "<<demand_k<<"  "<<"best_length "<<g.best.length<<" 代数"<<g.best_gen<<endl;


    ///去重方案1

    bool flag = remove_conflicts(demand_k, path_nodes, ok);
         if(g.best.length > INF_DIS)///如果大于最大值，是无解的情况
        return false;

    //bool flag = handle_conflicts_plan_2(demand_k, path_nodes);///去重方案2
    if(flag)///flag==true表示去重成功
    {
        return false;
    }

    if(demand_k == 0)
    {
        ADD_WEIGHT = g.best.length * PROB + 5;
        cout<<"add_weight    "<<ADD_WEIGHT<<endl;
    }
    for(int i = 0; i < city_num[demand_k]-1; i++)
    {
        int from = path_nodes[i];
        int to = path_nodes[i+1];
        ///这里的注释用于输出合法解的
        printf("%d ",hash_city[demand_k][from]);
        for(int j = 0; j < matrix_city[demand_k][from][to].path_num; j++)
        {
            int ans_path = matrix_city[demand_k][from][to].path[j];
            repeat[ans_path]++;
            ans_vector[demand_k].push_back(ans_path);
            if(demand_k == 0)
                add_weight(ans_path);///在这条边上加权值
            if(repeat[ans_path] == 2)
                repeat_vector.push_back(ans_path);///在重复边上加ans
            if(origin_edge[edge_hash[ans_path]].is_add == true && demand_k == 1)
            {
                add_cnt++;
            }
        }
        ///这里的注释用于输出合法解的
        for(int j = 0; j < matrix_city[demand_k][from][to].path_num-1; j++)
            printf("%d ", matrix_city[demand_k][from][to].path_node[j]);
    }
    puts("");
    double sub = 0;
    if(demand_k == 1)
        sub = add_cnt * ADD_WEIGHT;
    cout<<"best_length ==  "<<g.best.length - sub<<endl;
    best_weight += g.best.length;
    return true;
}
void search_route(char *topo[MAX_EDGE_NUM], int edge_num, char *demand[MAX_DEMAND_NUM], int demand_num)
{
    Group g1, g2;///种群1、2
    best_ans.best_ans_init();///最优解的初始化
    //NA_flag = false;
    add_cnt = 0;
    best_weight = 0;
    //LEVEL_UP = false;
    init_matrix();
    build_graph(topo, edge_num, demand, demand_num);

    build_city(demand, 0);
    compress_graph(0);
    //level_up(0);
    ans_vector[0].clear();
    ans_vector[1].clear();

    be_add_vector.clear();///被加边，也就是哪些边加了权值
    memset(repeat, 0, sizeof(repeat));
    repeat_vector.clear();

    g1.init(0);

    srand(time(NULL));

    int tsp_num = 0;
    //level_up(0);
    while(!tsp_solve(0, g1))
    {
        g1.update();
        if(g1.best.length > INF_DIS)
        {
            //cout<<"asas"<<endl;
            g1.init(0);
        }
        if(tsp_num++ == TSP_LIMIT)
        {
            compress_graph(0);
            level_up(0);
            g1.init(0);
        }
    }
    //cout<<tsp_num<<endl;

    build_city(demand, 1);
    compress_graph(1);//压缩第二个
    //level_up(1);
    //LEVEL_UP = true;
    g2.init(1);
    tsp_num = 0;
    while(!tsp_solve(1, g2))
    {
        g2.update();
        if(g2.best.length > INF_DIS)
        {
            //cout<<"asas"<<endl;
            g2.init(1);
        }
        if(tsp_num++ == TSP_LIMIT)
        {
            compress_graph(1);
            level_up(1);
            g2.init(1);
        }
    }
    //cout<<tsp_num<<endl;
    //printf("addd %d\n", add_cnt);
    best_ans.weight = best_weight - add_cnt*ADD_WEIGHT;
    best_ans.best_path[0] = ans_vector[0];
    best_ans.best_path[1] = ans_vector[1];
    best_ans.repeat_edge = repeat_vector.size();

    add_cnt = 0;
    best_weight = 0;

    //puts("");
    TSP_LIMIT = 50;
    if(!repeat_vector.empty()&&FLAG_DATA != 3)///如果重复边不为0,那么重复边加权值，重新降解
    {
        cout<<"add_weight    "<<ADD_WEIGHT<<endl;
        for(int i = 0; i < be_add_vector.size(); i++)
        {
            sub_weight(be_add_vector[i]);///减去之前的所加的权值
        }
        be_add_vector.clear();
        for(int i = 0; i < repeat_vector.size(); i++)
        {
            add_weight(repeat_vector[i]);
        }
        ans_vector[0].clear();
        ans_vector[1].clear();
        memset(repeat, 0, sizeof(repeat));
        repeat_vector.clear();
        compress_graph(0);
        g1.init(0);
        tsp_num = 0;
        while(!tsp_solve(0, g1))
        {
            g1.update();
            if(g1.best.length > INF_DIS)
            {
                //cout<<"asas"<<endl;
                g1.init(0);
            }
            if(tsp_num++ == TSP_LIMIT)
            {
                ///输出答案
                printf("repeat_size = %d weight = %d\n",best_ans.repeat_edge, best_ans.weight);
                for(int i = 0; i < best_ans.best_path[0].size(); i++)
                {
                    record_result(WORK_PATH, best_ans.best_path[0][i]);
                    printf("%d ",best_ans.best_path[0][i]);
                }
                puts("");
                for(int i = 0; i < best_ans.best_path[1].size(); i++)
                {
                    record_result(BACK_PATH, best_ans.best_path[1][i]);
                     printf("%d ",best_ans.best_path[1][i]);
                }
                return;
            }
        }
        compress_graph(1);
        g2.init(1);
        tsp_num = 0;
        while(!tsp_solve(1, g2))
        {
            g2.update();
            if(g2.best.length > INF_DIS)
            {
                //cout<<"asas"<<endl;
                g2.init(1);
            }
            if(tsp_num++ == TSP_LIMIT)
            {
                ///输出答案
                printf("repeat_size = %d weight = %d\n",best_ans.repeat_edge, best_ans.weight);
                for(int i = 0; i < best_ans.best_path[0].size(); i++)
                {
                    record_result(WORK_PATH, best_ans.best_path[0][i]);
                    printf("%d ",best_ans.best_path[0][i]);
                }
                puts("");
                for(int i = 0; i < best_ans.best_path[1].size(); i++)
                {
                    record_result(BACK_PATH, best_ans.best_path[1][i]);
                     printf("%d ",best_ans.best_path[1][i]);
                }
                return;
            }
        }
        //printf("addd %d\n", add_cnt);
        int now_weight = best_weight - add_cnt*ADD_WEIGHT;
        if(repeat_vector.size() < best_ans.repeat_edge)
        {
            best_ans.best_path[0] = ans_vector[0];
            best_ans.best_path[1] = ans_vector[1];
            best_ans.weight = now_weight;
            best_ans.repeat_edge = repeat_vector.size();
        }
        if(repeat_vector.size() == best_ans.repeat_edge)
        {

            if(now_weight < best_ans.weight)
            {
                best_ans.best_path[0] = ans_vector[0];
                best_ans.best_path[1] = ans_vector[1];
                best_ans.weight = now_weight;
                best_ans.repeat_edge = repeat_vector.size();
            }
        }
    }
///输出答案
    printf("repeat_size = %d weight = %d\n",best_ans.repeat_edge, best_ans.weight);
    for(int i = 0; i < best_ans.best_path[0].size(); i++)
    {
        record_result(WORK_PATH, best_ans.best_path[0][i]);
         printf("%d ",best_ans.best_path[0][i]);
    }
    puts("");
    for(int i = 0; i < best_ans.best_path[1].size(); i++)
    {
        record_result(BACK_PATH, best_ans.best_path[1][i]);
         printf("%d ",best_ans.best_path[1][i]);
    }

  ///保留
}
