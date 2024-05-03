#include<bits/stdc++.h>
#include<unordered_map>
using namespace std;
#define settype int
typedef pair<double, int> DI;
typedef pair<int, int> II;
typedef unordered_map<settype, double> USD;//from label sets to distances
typedef pair<settype, double> SD;
typedef pair<int, vector<SD>> IV;
const int MAX_V = 6262106;
int N, M;//# of vertices and edges
long long hopsize, npathConcat;//# of path concatenations
double optw = DBL_MAX;//optimal answer
int treeheight = 0, treewidth = 0, treeavgheight = 0;

typedef struct node{
    int level;//not used
    int ran;//rank in the order
    int parent;
    vector<int> children;
    vector<int> X;
};
node T[MAX_V];
unordered_map<int,vector<SD>> L[MAX_V];//supersets
vector<int> anc[MAX_V];
int root = -1;
unordered_map<int, USD> adj[MAX_V];//contains only edges to higher rank
unordered_map<int,int> adjo[MAX_V], adjT[MAX_V];//contains all the edges
bool allowedLabel[100];
settype allowedLabels;
int nsym, mapsym2ind[100];

void printset(settype a){
    int i = 0;
    while(a>0){
        if(a&1)
            printf("%c ", 'a'+i);
        i += 1;
        a = a >> 1;
    }
    cout << endl;
}
void printUSD(USD a){
    USD::iterator it;
    for (it = a.begin(); it != a.end(); it++){
        printset(it->first);
        printf("%f\n", it->second);
    }
}

vector<int> order;
bool flag[MAX_V];
bool cmp(const int &a, const int &b){
    return T[a].ran > T[b].ran;
}

vector<int> ordergen;
int del[MAX_V];//deleted neighbors
double update(int v){
//priorities for contracting vertices
    return 1000 * adjo[v].size() + del[v];
}
typedef pair<II, int> III;
void genorder(string filename, bool writeflag){
//first generating an order of contracting vertices
    priority_queue<II, vector<II>, greater<II> > degque;
    for (int i = 0; i < N; i++)
        degque.push(II(update(i), i));
    int iter = -1, totnewedge = 0;
    while(!degque.empty()){
        II ii = degque.top();
        degque.pop();
        int v = ii.second;
        if(flag[v])
            continue;
        double prio = update(v);
        if (prio > degque.top().first){//lazy update
            degque.push(II(prio,v));
            continue;
        }
        iter += 1;
        flag[v] = 1;
        ordergen.push_back(v);
        T[v].ran = iter;
        unordered_map<int, int>::iterator it;
        vector<int> nei;
        for (it = adjo[v].begin(); it !=adjo[v].end(); it++)
            if(!flag[it->first])
                nei.push_back(it->first);
        int lenX = nei.size();
        for (int j = 0; j < lenX; j++){
            int u = nei[j];
            for (int k = j + 1; k < lenX; k++){
                int w = nei[k];
                if(adjo[u].count(w)==0){
                    adjo[u][w] = 1;
                    adjo[w][u] = 1;
                    totnewedge += 1;
                }
            }
            //adjo[u].erase(v);
            del[u]++;
        }
    }
    if(writeflag){
        FILE *fp_order = fopen(filename.c_str(), "w");
        for (int i = 0; i < N;i++){
            fprintf(fp_order, "%d\n", T[i].ran);
        }
        fclose(fp_order);
    }
}

void LSDSJoin(USD &P1, USD &P2, USD &res){
    //return the res contains the paths of joining P1 and P2
    USD::iterator it1, it2;
    for (it1 = P1.begin(); it1 != P1.end(); it1++){
        settype set1 = it1->first;
        for (it2 = P2.begin(); it2 != P2.end(); it2++){
            settype set2 = it2->first;
            double dis = it1->second + it2->second;
            settype uni = set1 | set2;
            if(res.count(uni)){
                if(dis < res[uni])
                    res[uni] = dis;
            }
            else{
                res[uni] = dis;
            }
        }           
    }
}

void LSDSPrune(USD &res){
    vector<settype> era;
    USD::iterator it, jt;
    for (it = res.begin(); it != res.end();it++){
        for (jt = res.begin(); jt != res.end();jt++){
            settype s1 = it->first, s2 = jt->first;
            if (s2 == s1)
                continue;
            double dis1 = it->second, dis2 = jt->second;
            if (((s1 & s2) == s1) && (dis1 <= dis2)){
                era.push_back(s2);
            }
        }
    }
    for (int i = 0; i < era.size();i++)
        res.erase(era[i]);
}
double maxlabelsize, avglabelsize;
int descnt[MAX_V];
void treedec(){
    for (int i = 0; i < N; i++){
        int v = ordergen[i];
        if(i%100000==0)
            printf("%d\n", i);
        unordered_map<int, int>::iterator it;  
        for (it = adjT[v].begin(); it !=adjT[v].end(); it++)
            T[v].X.push_back(it->first);
        int lenX = T[v].X.size();
        for (int j = 0; j < lenX; j++){
            int u = T[v].X[j];
            for (int k = j + 1; k < lenX; k++){
                int w = T[v].X[k];
                if(T[u].ran<T[w].ran){
                    if(adjT[u].count(w)==0)
                        adjT[u][w] = 1;
                    LSDSJoin(adj[v][u], adj[v][w], adj[u][w]);
                    LSDSPrune(adj[u][w]);                 
                }
                else{
                    if(adjT[w].count(u)==0)
                        adjT[w][u] = 1;
                    LSDSJoin(adj[v][u], adj[v][w], adj[w][u]);
                    LSDSPrune(adj[w][u]);
                }
                
            }
        }
    }
    //from bottom to top
    for (int i = 0; i < ordergen.size();i++){
        int v = ordergen[i];
        sort(T[v].X.begin(), T[v].X.end(), cmp);
        int lenx = T[v].X.size();
        if (lenx != 0)
            T[v].parent = T[v].X[lenx - 1];
        else
            T[v].parent = MAX_V;
        //printf("%d %d\n", v + 1, T[v].parent + 1);
        T[v].X.push_back(v);
        treewidth = max(treewidth, lenx + 1);
        if (T[v].parent == MAX_V){
            root = v;
            break;
        }
        T[T[v].parent].children.push_back(v);
        descnt[v]++;
        descnt[T[v].parent] += descnt[v];
    }
}
bool cmpSD(const SD &a, const SD &b){
    return a.second < b.second;
}
queue<int> bfs, bfssave;
long long indexsize, totalwidth;
void labeling(){
    //label in a top-down manner
    for (int i = N - 2; i >= 0; i--){
        int v = ordergen[i];
        if(i%100000==0)
            printf("%d\n", i);
        int lenX = T[v].X.size();
        for (int j = 0; j < lenX; j++){
            int u = T[v].X[j];
            if (u == v)
                continue;
            for (int k = 0; k < lenX; k++){
                int w = T[v].X[k];
                if (w == v || w == u)
                    continue;
                USD tmp;
                if(T[u].ran<T[w].ran){
                    LSDSJoin(adj[v][w], adj[u][w], adj[v][u]);
                    LSDSPrune(adj[v][u]);
                }
                else{
                    LSDSJoin(adj[v][w], adj[w][u], adj[v][u]);
                    LSDSPrune(adj[v][u]);
                }
            }
            USD::iterator it;
            for (it = adj[v][u].begin(); it != adj[v][u].end();it++){
                L[v][u].push_back(SD(it->first, it->second));
            }
            maxlabelsize = max(maxlabelsize, (double)L[v][u].size());
            avglabelsize += (double)L[v][u].size();
            sort(L[v][u].begin(), L[v][u].end(), cmpSD);
            //printf("%d %d:\n", v+1,u+1);
            //printSD(L[v][u]);
        }
        totalwidth += lenX;
    }
}

void save(string filename){
    filename += string("LSDindex");
    ofstream of;
    of.open(filename.c_str(), ios::binary);
    // FILE *fp_index=fopen("index.txt","w");
    // fprintf(fp_index, "%d ", N);
    of.write(reinterpret_cast<const char *>(&N), sizeof(int));
    bfssave.push(root);
    while(!bfssave.empty()){
        int v = bfssave.front();
        bfssave.pop();
        //printf("%d\n", v);
        int nx = T[v].X.size();
        indexsize += 3 + nx;
        //fprintf(fp_index, "%d %d %d %d%c", v, T[v].parent, nx, lenl,' ');
        of.write(reinterpret_cast<const char *>(&v), sizeof(int));
        of.write(reinterpret_cast<const char *>(&T[v].parent), sizeof(int));
        of.write(reinterpret_cast<const char *>(&nx), sizeof(int));
        for (int i = 0; i < nx; i++){
            //fprintf(fp_index, "%d%c", T[v].X[i].first, (i == nx - 1) ? ' ' : ' ');
            of.write(reinterpret_cast<const char *>(&T[v].X[i]), sizeof(int));
            int u = T[v].X[i];
            if(u==v)
                continue;
            USD::iterator it;
            for (it = adj[v][u].begin(); it != adj[v][u].end();it++){
                indexsize += 3;
                of.write(reinterpret_cast<const char *>(&it->first), sizeof(int));
                of.write(reinterpret_cast<const char *>(&it->second), sizeof(double));
            }
        }
        for (int i = 0; i < T[v].children.size();i++){
            bfssave.push(T[v].children[i]);
        }
    }
    //fclose(fp_index);
    of.close();
}

double dist(int u, int v, settype s){
    if(T[u].ran>T[v].ran)
        swap(u, v);
    for (int i = 0; i < L[u][v].size(); i++){
        settype s1 = L[u][v][i].first;
        if ((s1 & s) == s1)
            return L[u][v][i].second;
    }
    return DBL_MAX;
}

double ds[MAX_V], dt[MAX_V];
double LSDQuery(int s, int t){
    optw = DBL_MAX;
    if (s == t)
        return 0;
    s--, t--;
    vector<int> ancs, anct;
    int u1 = s, l = -1;
    while (u1 != MAX_V){
        ancs.push_back(u1);
        u1 = T[u1].parent;
    }
    u1 = t;
    while (u1 != MAX_V){
        anct.push_back(u1);
        u1 = T[u1].parent;
    }
    int i = ancs.size() - 1, j = anct.size() - 1, k = -1;
    unordered_map<int, int> inds, indt;
    while (i != -1 && j != -1){
        if (ancs[i] == anct[j]){
            inds[ancs[i]] = i;
            indt[anct[j]] = j;
            i--, j--, k++;
        }
        else
            break;
    }
    if(i==-1)
        l = ancs[0];
    else if(j==-1)
        l = anct[0];
    else
        l = ancs[i + 1];
    int ind;
    for (int i = 0; i < MAX_V;i++){
        ds[i] = dt[i] = DBL_MAX;
    }
    ds[s] = 0;
    dt[t] = 0;
    for (int i = 0; i + 1 < T[s].X.size(); i++){
        int w = T[s].X[i];
        ds[w] = dist(s, w, allowedLabels);
    }
    for (int i = 0; i + 1 < T[t].X.size(); i++){
        int w = T[t].X[i];
        dt[w] = dist(t, w, allowedLabels);
    }
    int s_ = s;
    while(s_!=l){
        int p = T[s_].parent;
        vector<int> su, sv;
        for (int i = 0; i < T[p].X.size(); i++){
            int u = T[p].X[i];
            bool existflag = false;
            for (int j = 0; j < T[s_].X.size();j++){
                int v = T[s_].X[j];
                if(v==u){
                    existflag = true;
                    break;
                }
            }
            if(existflag)
                sv.push_back(u);
            else
                su.push_back(u);
        }
        for (int i = 0; i < su.size();i++)
            for (int j = 0; j < sv.size();j++){
                int u = su[i], v = sv[j];
                ds[u] = min(ds[u], ds[v] + dist(v, u, allowedLabels));
            }
        s_ = p;
    }
    int t_ = t;
    while(t_!=l){
        int p = T[t_].parent;
        vector<int> tu, tv;
        for (int i = 0; i < T[p].X.size(); i++){
            int u = T[p].X[i];
            bool existflag = false;
            for (int j = 0; j < T[t_].X.size();j++){
                int v = T[t_].X[j];
                if(v==u){
                    existflag = true;
                    break;
                }
            }
            if(existflag)
                tv.push_back(u);
            else
                tu.push_back(u);
        }
        for (int i = 0; i < tu.size();i++)
            for (int j = 0; j < tv.size();j++){
                int u = tu[i], v = tv[j];
                dt[u] = min(dt[u], dt[v] + dist(v, u, allowedLabels));
            }
        t_ = p;
    }
    for (int i = 0; i < T[l].X.size(); i++){
        int w = T[l].X[i];
        optw = min(optw, ds[w] + dt[w]);
    }
    // printf("%f\n", optw);
    if (optw == DBL_MAX)
        optw = -1;
    return optw;
}

struct edge{
    int from, to;
    double weight;
    char label;
    edge(int a,int b,double w,char l){
        from = a, to = b, weight = w, label = l;
    }
};

vector<edge> alledges;
int main(int argc , char * argv[]){
    string sfile, sq, regL, srandom;
    FILE *fp_query, *fp_network;
    if (argc > 1)
        sfile = string(argv[1]);
    else
        sfile = string("NYC");
    if (argc > 2)
        sq = string(argv[2]);
    else
        sq = string("q1");
    if (argc > 3)
        regL = string(argv[3]);
    else
        regL = string("A2*D1*A2*");
    string prefix = string("../data/") + sfile + string("/");
    string graphfile = prefix + string("USA-road-l.") + sfile + (".gr");
    fp_network = fopen(graphfile.c_str(), "r");
    char ch, buffer[100];
    int u, v, cat2;
    double w;
    char cat1;
    //read graph
    for (int i = 0; i < 4; i++)
        fgets(buffer, 90, fp_network);
    for (int i = 0; i < 4; i++)
        fgetc(fp_network);
    fscanf(fp_network, "%d%d", &N, &M);
    for (int i = 0; i < 3; i++)
        fgets(buffer, 90, fp_network);
    for (int i = 0; i < M; i++) {
        fscanf(fp_network, "%c%d%d%lf%c%c%d", &ch, &u, &v, &w, &cat1, &cat1, &cat2);
        fgets(buffer, 90, fp_network);
        u--;
        v--;
        cat2 = (cat2 > 5) ? 5 : cat2;
        char l = (cat1 - 'A') * 5 + cat2 - 1 + 'a';
        //printf("%d %d %c%d %c\n", u, v, cat1, cat2, l);
        if (i % 2 == 0){
            adjo[u][v]=1;
            adjo[v][u]=1;
            alledges.push_back(edge(u, v, w, l));
        }
    }
    
    for (int i = 0; i < regL.size() - 1; i++){
        if (regL[i] == '(' || regL[i] == ' ')
            continue;
        int cat2 = regL[i + 1] - '0';
        cat2 = (cat2 > 5) ? 5 : cat2;
        char cat1 = regL[i];
        char l = (cat1 - 'A') * 5 + cat2 - 1 + 'a';
        if (allowedLabel[l - 'a'] == 0){
            allowedLabels = allowedLabels | (1 << (l - 'a'));
            nsym += 1;
        }
        allowedLabel[l - 'a'] = 1;
        i += 2;
    }
    printset(allowedLabels);

    std::chrono::high_resolution_clock::time_point t1, t2;
	std::chrono::duration<double> time_span;
	double runT;
    t1=std::chrono::high_resolution_clock::now();
    string ordername = string("../data/") + sfile + string("/") + string("order.txt");
    if(0){//generate order for vertices
        genorder(ordername, 1);
    }
    else{//get order from file
        ordergen.assign(N, -1);
        FILE *fpord = fopen(ordername.c_str(), "r");
        for (int i = 0; i < N; i++){
            fscanf(fpord, "%d", &T[i].ran);
            ordergen[T[i].ran] = i;
        }
    }
    t2 = std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Order Generation Time "<<runT<<endl;

    // distribute edges
    for (int i = 0; i < alledges.size(); i++)
    {
        int f = alledges[i].from, t = alledges[i].to;
        double w = alledges[i].weight;
        if(T[f].ran>T[t].ran)
            swap(f, t);
        adjT[f][t] = 1;
        adj[f][t][1 << (alledges[i].label - 'a')] = w;
        //printf("%d %d:\n", f, t);
        //printUSD(adj[f][t]);
    }
    string setres;

    t1=std::chrono::high_resolution_clock::now();
    treedec();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Tree Decomposition Time "<<runT<<endl;
    cout << "Tree Width " << treewidth << endl;
    setres += string("Tree Decomposition Time ") + to_string(runT)+ string("\n");

    t1=std::chrono::high_resolution_clock::now();
    labeling();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Labeling Time "<<runT<<endl;
    cout << "Max. Label Size " << maxlabelsize << endl;
    cout << "Avg. Label Size " << (double)avglabelsize / totalwidth << endl;
    setres += string("Labeling Time ") + to_string(runT) + string("\n");
    setres += string("Tree Width ") + to_string(treewidth) + string("\n");    
    setres += string("Max. Label Size ") + to_string(maxlabelsize) + string("\n");
    setres += string("Avg. Label Size ") + to_string((double)avglabelsize / totalwidth) + string("\n");

    t1 = std::chrono::high_resolution_clock::now();
    save(string("../data/") + sfile + string("/"));// test without save
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
    cout << "Saving Time " << runT << endl;
    cout << "Index Size " << (double)indexsize * 4 / 1000000 << "MB" << endl;
    setres += string("Saving Time ") + to_string(runT) + string("\n");
    setres += string("Index Size ") + to_string((double)indexsize * 4 / 1000000) + string("MB\n");
    cout << endl << "Querying... " << endl;
    for (int qi = 0; qi < 1; qi++){
        vector<II> queryset;
        vector<double> ans;
        string s3 = string("../data/") + sfile + string("/") + string("q") + to_string(qi + 1);
        fp_query = fopen(s3.c_str(), "r");
        int qs, qt;
        while (~fscanf(fp_query, "%d%d", &qs, &qt)){
            queryset.push_back(II(qs, qt));
        }
        fclose(fp_query);
        int qn = queryset.size();
        t1=std::chrono::high_resolution_clock::now();
        for (int i = 0; i < queryset.size(); i++){
            ans.push_back(LSDQuery(queryset[i].first, queryset[i].second));
        }
        t2=std::chrono::high_resolution_clock::now();
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT= time_span.count();
    }
    for (int qi = 0; qi < 10; qi++){
        vector<II> queryset;
        vector<double> ans;
        string s3 = string("../data/") + sfile + string("/") + string("q") + to_string(qi + 1);
        fp_query = fopen(s3.c_str(), "r");
        int qs, qt;
        while (~fscanf(fp_query, "%d%d", &qs, &qt)){
            queryset.push_back(II(qs, qt));
        }
        fclose(fp_query);
        int qn = queryset.size();
        t1=std::chrono::high_resolution_clock::now();
        for (int i = 0; i < qn; i++){
            ans.push_back(LSDQuery(queryset[i].first, queryset[i].second));
        }
        t2=std::chrono::high_resolution_clock::now();
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT= time_span.count();
        cout << (string("q") + to_string(qi + 1)).c_str() << "Query Time\n" << runT*1000 << endl;
        setres += string("q") + to_string(qi + 1);
        setres += string(" Query Time \n") + to_string(runT*1000) + string("\n");

        FILE *fp_out = fopen((prefix + sfile + string("q") + to_string(qi + 1) + string("LSDResults")).c_str(), "w");
        for (int i = 0; i < ans.size(); i++)
            fprintf(fp_out, "%f\n", ans[i]);
        fclose(fp_out);
        setres += string("\n");
    }

    FILE *fp_record = fopen("LSDRecord.txt", "a");
    fprintf(fp_record, "%s %s\n", sfile.c_str(),regL.c_str());
    fprintf(fp_record, "%s\n", setres.c_str());
    fclose(fp_record);
    return 0;
}
