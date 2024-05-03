#include "Regex2MinDFA.h"
#include<bits/stdc++.h>
#include<unordered_map>
using namespace std;
#define eps 1e-8
#define showstat
#define INF 0x3f3f3f3f
typedef pair<double, int> DI;
typedef pair<int, int> II;
typedef struct uiid{
    int z[MAX_es][MAX_es];
    uiid(){
        memset(z, INF, sizeof(z));
    }
}UIID;//mapping state q q' to distance for P_vw and P_wv
typedef pair<int, UIID> IV;
const int MAX_V = 6262106;// 3598633;
int N, M;//# of vertices and edges
long long hopsize, npathConcat;//# of hoplinks and path concatenations
int optw = INF;//optimal answer
int treeheight = 0, treewidth = 0;
double treeavgheight = 0;

typedef struct node{
    int level;//not used
    int ran;//rank in the order
    int parent;
    vector<int> children;
    vector<int> X;
};
node T[MAX_V];
vector<IV> L1[MAX_V], L2[MAX_V];//supersets //mapping state q q' to distance for P_vw and P_wv
vector<int> L1maxw[MAX_V], L2maxw[MAX_V];
int root = -1;
unordered_map<int, UIID> adj[MAX_V];//contains only edges to higher rank
unordered_map<int,int> adjo[MAX_V], adjT[MAX_V];//contains all the edges
typedef unordered_map<int, int> HID;
typedef unordered_map<int, HID> HIID;
HIID char2mat[27];//from an edge label to all transitions
DFA minDfa;
int DFAq0 = 0;
void Reg2minDFA(string str1){
	//string str = "(a|b)*abb";
	//string str = "(a|b)*c|z*";
    string oristr = "";
	//transform the label to a letter
    for (int i = 0; i < str1.size();i++){
        if (str1[i] == ' ')
            continue;
        if (str1[i] >= 'A' && str1[i] <= 'D'){
            int cat2 = str1[i + 1] - '0';
            cat2 = (cat2 > 5) ? 5 : cat2;
            char l = (str1[i] - 'A') * 5 + cat2 - 1 + 'a';
            oristr += l;
            i++;
        }
        else
            oristr += str1[i];
    }
    string str = infixToSuffix(oristr);
	int i, j;
	//NFA DFA initialization
	for(i = 0; i < MAX_NS; i++){
		NfaStates[i].index = i;
		NfaStates[i].input = '#';
		NfaStates[i].chTrans = -1;
	}
	for(i = 0; i < MAX_NS; i++){
		DfaStates[i].index = i;
		DfaStates[i].isEnd = false;
		for(j = 0; j < 100; j++){
			DfaStates[i].Edges[j].input = '#';
			DfaStates[i].Edges[j].Trans = -1;
		}
	}
	for(i = 0; i < MAX_NS; i++){
		minDfaStates[i].index = i;
		minDfaStates[i].isEnd = false;
		for(int j = 0; j < 100; j++)
		{
			minDfaStates[i].Edges[j].input = '#';
			minDfaStates[i].Edges[j].Trans = -1;
		}
	}
	
	NFA n = strToNfa(str);//string to NFA
	//printNFA(n);
	DFA d = nfaToDfa(n, str);//NFA to DFA
	//printDFA(d);
	minDfa = minDFA(d);//DFA minimization
	printMinDFA(minDfa);
    string teststr = "bbbpppppp";
    printf("%s: %d DFA states\n", oristr.c_str(), minDfaStateNum);
    printf("%s test:%d\n", teststr.c_str(), indicator(minDfa, teststr));
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

void PCSPJoin(UIID &P1, UIID &P2, UIID &res){
    //return the res contains the paths of joining P1 and P2
    for (int q1 = 0; q1 < MAX_es; q1++){
        for (int q1_ = 0; q1_<MAX_es; q1_++){
            if(P1.z[q1][q1_]!=INF){
                for (int q2_=0; q2_<MAX_es; q2_++){
                    if(P2.z[q1_][q2_]!=INF){
                        res.z[q1][q2_] = min(res.z[q1][q2_], P1.z[q1][q1_] + P2.z[q1_][q2_]);
                    }
                }
            }            
        }
    }
}

int descnt[MAX_V];
void treedec(){
	//follow the order to do MDE algorithm
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
                    PCSPJoin(adj[u][v], adj[v][w], adj[u][w]);
                    PCSPJoin(adj[w][v], adj[v][u], adj[w][u]);
                }
                else{
                    if(adjT[w].count(u)==0)
                        adjT[w][u] = 1;
                    PCSPJoin(adj[u][v], adj[v][w], adj[u][w]);
                    PCSPJoin(adj[w][v], adj[v][u], adj[w][u]);
                }
            }
        }
    }
    //from bottom to top set the parent
    for (int i = 0; i < ordergen.size();i++){
        int v = ordergen[i];
        sort(T[v].X.begin(), T[v].X.end(), cmp);
        int lenx = T[v].X.size();
        if (lenx != 0)
            T[v].parent = T[v].X[lenx - 1];
        else
            T[v].parent = MAX_V;
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
    for (int i = 0; i < N;i++){
        adjo[i].clear();
        adjT[i].clear();
    }
}

queue<int> bfs, bfssave;
long long indexsize, pindexsize;
vector<int> ancarray[MAX_V];//the indices (or depth) for X(v)'s nodes
void generateLabel4v(int v){
    //generate labels for each X(v) and its ancestors 
    vector<int> anc;
    int u1 = v;
    while (T[u1].parent != MAX_V){
        anc.push_back(T[u1].parent);
        u1 = T[u1].parent;
    }
    int lenanc = anc.size();
    treeavgheight += (double)lenanc;
    treeheight = max(treeheight, lenanc + 1);
    for (int i = 0; i < lenanc;i++){
        int u = anc[anc.size() - 1 - i];
        int lenx = T[v].X.size();
        UIID res1 = adj[v][u], res2 = adj[u][v]; // up, down
        for (int j = 0; j < lenx;j++){
            int w = T[v].X[j];
            if (w == v || w == u){
                if (w == u)
                    ancarray[v].push_back(i);
                continue;
            }
            if (T[w].ran <= T[u].ran){
                PCSPJoin(adj[v][w], L1[w][i].second, res1); //vw wu
                PCSPJoin(L2[w][i].second, adj[w][v], res2);//uw wv
            }
            else{//w>u, w has been in j-th ancarray //ancarray[v][j] not used because need sorting ancarray
                PCSPJoin(adj[v][w], L2[u][ancarray[v][j]].second, res1);//vw wu
                PCSPJoin(L1[u][ancarray[v][j]].second, adj[w][v], res2);//uw wv
            }
        }
        L1[v].push_back(IV(u, res1));//vu
        L2[v].push_back(IV(u, res2));//uv
        //printf("%d %d:\n", v+1, u+1);
        //printUIID(res1);
        //printUIID(res2);
    }
    UIID tmpv;
    L1[v].push_back(IV(v, tmpv));
    L2[v].push_back(IV(v, tmpv));
    ancarray[v].push_back(anc.size());
    //for (int j = 0; j < ancarray[v].size();j++)
    //    printf("anc%d ", ancarray[v][j]);
    //cout << L[v].size() << endl;
}
double maxlabelsize, avglabelsize;
void labeling(){
    //label in a top-down manner
    bfs.push(root);
    int iter = 0;
    while(!bfs.empty()){
        int v= bfs.front();
        bfs.pop();
        //sort(T[v].X.begin(), T[v].X.end(), cmp);
        generateLabel4v(v);
        for (int i = 0; i < T[v].children.size();i++){
            bfs.push(T[v].children[i]);
        }
        if(iter%100000==0)
            printf("%d %d\n", iter, treeheight);
        iter += 1;
    }
    printf("Extract Two Sets\n");
    //extract the two sets from supersets
    for (int i = 0; i <= N; i++){
        for (int j = 0; j < L1[i].size();j++){
            double PL1labelsize = 0;
            int maxw = INF;
            for (int q_ = 0; q_ < MAX_es; q_++){
                if(finalFlag[q_]){
                    int d1 = L1[i][j].second.z[DFAq0][q_];
                    if(d1!=INF){
                        maxw = min(maxw, d1);
                        PL1labelsize++;
                    }
                }
            }
            L1maxw[i].push_back(maxw);
            maxlabelsize = max(maxlabelsize, (double)PL1labelsize);
            avglabelsize += PL1labelsize / 2;
        }
        for (int j = 0; j < L2[i].size();j++){
            double PL2labelsize = 0;
            int maxw = INF;
            for (int q_ = 0; q_ < MAX_es; q_++){
                if(finalFlag[q_]){
                    int d1 = L2[i][j].second.z[DFAq0][q_];
                    if(d1!=INF){
                        maxw = min(maxw, d1);
                        PL2labelsize++;
                    }
                }
            }
            L2maxw[i].push_back(maxw);
            maxlabelsize = max(maxlabelsize, (double)PL2labelsize);
            avglabelsize += PL2labelsize / 2;
        }
    }
}

vector<int> flagHs[30][MAX_V], flagHt[30][MAX_V];
int map2sep[MAX_V];
void sepPrune(int top, int i4H){
    //printf("Prune for Separator %d with index %d\n", top+1, i4H);
    map2sep[top] = i4H;
    vector<int> TX = T[top].X;
    queue<int> bfsdesc;
    int v = top;
    for (int i = 0; i < T[v].children.size();i++)
        bfsdesc.push(T[v].children[i]);
    while(!bfsdesc.empty()){
        int v = bfsdesc.front();
        bfsdesc.pop();
        for (int i = 0; i < T[v].children.size();i++){
            bfsdesc.push(T[v].children[i]);
        }
        for (int i = 0; i + 1 < ancarray[top].size(); i++)
            flagHs[i4H][v].push_back(0);
        for (int i = 0; i + 1 < ancarray[top].size(); i++){
            int indh = ancarray[top][i];
            int h = L1[top][indh].first;
            bool pruneflagh = true;
            bool forpruneflag = false;
            for (int q = 0; q < MAX_es; q++){
                int dis = L1[v][indh].second.z[DFAq0][q];
                if(dis!=INF){
                    bool conditionflagq = false;
                    forpruneflag = true;
                    for (int j = 0; j + 1 < ancarray[top].size(); j++)
                    {
                        if (j == i)
                            continue;
                        int indh_ = ancarray[top][j];
                        if(flagHs[i4H][v][j])
                            continue;
                        int h_ = L1[top][indh_].first;
                        UIID res;
                        if(T[h_].ran<T[h].ran)
                            PCSPJoin(L1[v][indh_].second, L1[h_][indh].second, res);
                        else
                            PCSPJoin(L1[v][indh_].second, L2[h][indh_].second, res);
                        if(res.z[DFAq0][q]!=INF){
                            if(abs(res.z[DFAq0][q]-dis)<eps){
                                conditionflagq = true;
                                break;
                            }
                        }
                    }
                    //printf("prune %d %d %d %d %f %d\n", top + 1, v + 1, h + 1, q, dis, conditionflagq);
                    if (conditionflagq == false){
                        pruneflagh = false;
                        break;
                    }
                }
            }
            if(forpruneflag==false)
                pruneflagh = false;
            flagHs[i4H][v][i] = pruneflagh;
            //printf("------%d %d %d %d---------\n", top + 1, v + 1, h + 1, pruneflagh);
        }
    }
    /*
    for (int i = 0; i <= N;i++){
        if(flagHs[i4H][i].size()!=0){
            for (int j = 0; j + 1 < ancarray[top].size();j++)
                if (flagHs[i4H][i][j])
                    printf("======%d %d %d %d======\n", top + 1, i + 1, j, L1[top][ancarray[top][j]].first+1);
        }
    }*/
}

int freq[MAX_V], K;
vector<DI> sortH;
void preprocessPrunedSep(double alpha){
    memset(map2sep, -1, sizeof(map2sep));
    int tothit = 0;
    default_random_engine gen(time(NULL));
    uniform_int_distribution<int> st(0, N - 1);
    for (int nq = 0; nq < 1000000; nq++){//use 1000000 queries to find top-K frequent separators
        int s = st(gen), t = st(gen);
        if (s == t)
            continue;
        vector<int> ancs,anct;
        int u1 = s, l = -1;
        while(u1!=MAX_V){
            ancs.push_back(u1);
            u1 = T[u1].parent;
        }
        u1 = t;
        while(u1!=MAX_V){
            anct.push_back(u1);
            u1 = T[u1].parent;
        }
        int i = ancs.size() - 1, j = anct.size() - 1, k = -1;
        while (i != -1 && j != -1){
            if (ancs[i] == anct[j]){
                i--,j--,k++;
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
        if (l == s||l == t){
            continue;
        }
        else{
            int cs = ancs[i], ct = anct[j];
            l = (ancarray[cs].size() < ancarray[ct].size()) ? cs : ct;
            if(ancarray[cs].size()==ancarray[ct].size())
                l = (cs < ct) ? cs : ct;
            freq[l] += 1;
            tothit++;
        }
    }
    for (int i = 0; i <= N;i++){
        if (freq[i] != 0){
            sortH.push_back(DI((double)freq[i]/(double)tothit, i));
        }
    }
    sort(sortH.begin(), sortH.end());
    double sum = 0;
    K = 0;
    for (int i = sortH.size() - 1; i >= 0; i--){
        sum += sortH[i].first;
        K++;
        //printf("Top%d Freq %f %f %d\n", sortH.size() - i, sortH[i].first, sum, sortH[i].second + 1);
        if (sum>alpha)
            break;
    }
    printf("Top%d sum%f\n", K, sum);
    K = min(K, 20);
    for (int i = 0; i < K; i++){
        sepPrune(sortH[sortH.size() - 1 - i].second, i);
    }
}

void save(string filename){
    filename += string("PCSPindex");
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
        int lenl1 = L1[v].size(), lenl2 = L2[v].size(), nx = T[v].X.size();
        indexsize += 5 + nx;
        //fprintf(fp_index, "%d %d %d %d%c", v, T[v].parent, nx, lenl,' ');
        of.write(reinterpret_cast<const char *>(&v), sizeof(int));
        of.write(reinterpret_cast<const char *>(&T[v].parent), sizeof(int));
        of.write(reinterpret_cast<const char *>(&nx), sizeof(int));
        of.write(reinterpret_cast<const char *>(&lenl1), sizeof(int));
        of.write(reinterpret_cast<const char *>(&lenl2), sizeof(int));
        for (int i = 0; i < nx; i++){
            //fprintf(fp_index, "%d%c", T[v].X[i].first, (i == nx - 1) ? ' ' : ' ');
            of.write(reinterpret_cast<const char *>(&T[v].X[i]), sizeof(int));
        }
        for (int i = 0; i < lenl1; i++){
            int lend = MAX_es, tmp = (L1maxw[v][i]==INF)?-1:L1maxw[v][i];
            indexsize += 3 + lend;
            //fprintf(fp_index, "%d %d ", L[v][i].first, lend);
            of.write(reinterpret_cast<const char *>(&tmp), sizeof(int));
            of.write(reinterpret_cast<const char *>(&lend), sizeof(int));
            int flag = 0;
            for (int q = 0; q < MAX_es;q++){
                int tmpi = (L1[v][i].second.z[DFAq0][q]==INF)?-1:L1[v][i].second.z[DFAq0][q];
                flag = flag | (1 << q);
                of.write(reinterpret_cast<const char *>(&tmpi), sizeof(int));
            }
            of.write(reinterpret_cast<const char *>(&flag), sizeof(int));
        }
        for (int i = 0; i < lenl2; i++){
            int lend = MAX_es, tmp = (L2maxw[v][i]==INF)?-1: L2maxw[v][i];
            indexsize += 3 + lend;
            //fprintf(fp_index, "%d %d ", L[v][i].first, lend);
            of.write(reinterpret_cast<const char *>(&tmp), sizeof(int));
            of.write(reinterpret_cast<const char *>(&lend), sizeof(int));
            int flag = 0;
            for (int q = 0; q < MAX_es;q++){
                int tmpi = (L2[v][i].second.z[DFAq0][q]==INF)?-1:L2[v][i].second.z[DFAq0][q];
                flag = flag | (1 << q);
                of.write(reinterpret_cast<const char *>(&tmpi), sizeof(int));
            }
            of.write(reinterpret_cast<const char *>(&flag), sizeof(int));
        }
        //fprintf(fp_index, "\n");
        //sort(T[v].X.begin(), T[v].X.end(), cmp);
        for (int i = 0; i < T[v].children.size();i++){
            bfssave.push(T[v].children[i]);
        }
    }
    for (int i4H = 0; i4H < K; i4H++){
        for (int i = 0; i <= N; i++)
        {
            pindexsize += (long long)flagHs[i4H][i].size();
            for (int j = 0; j < flagHs[i4H][i].size(); j++){
                int tmp = flagHs[i4H][i][j];
                of.write(reinterpret_cast<const char *>(&tmp), sizeof(int));
            }
        }
    }
    //fclose(fp_index);
    of.close();
}

long long pruneHoplinks, totlca, prunepc, totpc;
int PCSPQueryIPrune(int s, int t){
    optw = INF;
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
    if (l == s){//X(s) is an ancestor of X(t)
        optw = L2maxw[t][ancs.size() - 1];
    }
    else if (l == t){//X(t) is an ancestor of X(s)
        optw = L1maxw[s][anct.size() - 1];
    }
    else{//find the LCA and cs and ct
        int cs = ancs[i], ct = anct[j];
        l = (ancarray[cs].size() < ancarray[ct].size()) ? cs : ct;
        if(ancarray[cs].size()==ancarray[ct].size())
            l = (cs < ct) ? cs : ct;
        hopsize += ancarray[l].size() - 1;
        #ifdef showstat
        totlca++;
        #endif
        //printf("-%d %d %d-\n", l + 1, s+1, map2sep[l]);
        for (int i = 0; i + 1 < ancarray[l].size(); i++)//iterate over each hoplink
        {
            ind = ancarray[l][i];
            if(map2sep[l]!=-1&&flagHs[map2sep[l]][s].size()!=0&&flagHs[map2sep[l]][s][i]==1){
                //judge whether to use the pruning
                //printf("Prune %d %d %d %d\n", s+1, t+1, l+1, L1[s][ind].first+1);
                #ifdef showstat
                pruneHoplinks++;
                prunepc += MAX_es;
                #endif
                continue;
            }
            for (int q = 0;q<MAX_es;q++){
                int d1 = L1[s][ind].second.z[DFAq0][q];
                if(d1!=INF){
                    for (int q_ = 0;q_<MAX_es;q_++){
                        if(finalFlag[q_]){
                            int d2 = L2[t][ind].second.z[q][q_];
                            if(d2!=INF){
                                optw = min(optw, d1 + d2);
                                totpc++;
                            }
                        }
                    }
                }
            }
        }
    }
    //printf("%f\n", optw);
    if(optw==INF)
        optw = -1;
    return optw;
}

struct edge{
    int from, to;
    int weight;
    char label;
    edge(int a,int b,int w,char l){
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
    if (argc > 4)
        srandom = string(argv[4]);
    else
        srandom = string("0.94");
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
        //printf("%d %d %d %c%d %c\n", u, v, (int)(w), cat1, cat2, l);
        if (i % 2 == 0){
            adjo[u][v]=1;
            adjo[v][u]=1;
            alledges.push_back(edge(u, v, (int)(w*100), l));
        }
    }
	//regular expression to minimized DFA
    Reg2minDFA(regL);
    cout << endl;
    DFAq0 = minDfa.startState;
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
    
    //single char to matrix
    for (int i = 0; i < 26;i++){
        if(minDfa.terminator.count(i + 'a')){
            for (int j = 0; j < minDfaStateNum;j++){
                int toS = minDfa.trans[j][i];
                if(toS != -1){
                    char2mat[i][j][toS] = -1;
                }                    
            }
        }
    }

    // distribute edges
    for (int i = 0; i < alledges.size(); i++)
    {
        int f = alledges[i].from, t = alledges[i].to;
        int w = alledges[i].weight;
        if(T[f].ran>T[t].ran)
            swap(f, t);
        adjT[f][t] = 1;
        HIID tmp = char2mat[alledges[i].label-'a'];
        HIID::iterator it;
        for (it = tmp.begin(); it != tmp.end();it++){
            HID::iterator iit;
            for (iit = it->second.begin(); iit != it->second.end(); iit++){
                adj[f][t].z[it->first][iit->first] = w;
            }
        }
        adj[t][f] = adj[f][t];
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
    cout<<"Tree Height "<<treeheight<<endl;
    cout<<"Tree Avg. Height "<<treeavgheight/N<<endl;
    cout << "Max. Label Size " << maxlabelsize << endl;
    cout << "Avg. Label Size " << avglabelsize / treeavgheight << endl;
    setres += string("Labeling Time ") + to_string(runT) + string("\n");
    setres += string("Tree Width ") + to_string(treewidth) + string("\n");    
    setres += string("Tree Height ") + to_string(treeheight) + string("\n");   
    setres += string("Tree Avg. Height ") + to_string(treeavgheight/N) + string("\n");
    setres += string("Max. Label Size ") + to_string(maxlabelsize) + string("\n");
    setres += string("Avg. Label Size ") + to_string(avglabelsize / treeavgheight) + string("\n");

    cout << endl;
    double alpha = stof(srandom.c_str());
    if (argc > 4 && alpha > 0){//Separator Pruning
        cout << "Pruning... " << endl;
        t1 = std::chrono::high_resolution_clock::now();
        preprocessPrunedSep(alpha);
        t2=std::chrono::high_resolution_clock::now();
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT= time_span.count();
        cout << "Pruning Index Time " << runT << endl;
        setres += string("Pruning Index Time ") + to_string(runT) + string("\n");
    }

    t1 = std::chrono::high_resolution_clock::now();
    save(string("../data/") + sfile + string("/"));// test without save
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
    cout << "Saving Time " << runT << endl;
    cout << "Index Size " << (double)indexsize * 4 / 1000000 << "MB" << endl;
    cout << "Pruning Index Size " << (double)pindexsize * 4 / 1000000 << "MB" << endl;
    setres += string("Saving Time ") + to_string(runT) + string("\n");
    setres += string("Index Size ") + to_string((double)indexsize * 4 / 1000000) + string("MB\n");
    setres += string("Pruning Index Size ") + to_string((double)pindexsize * 4 / 1000000) + string("MB\n");

    cout << endl << "Querying... " << endl;

    for (int qi = 0; qi < 1; qi++){//test a queryset
        vector<II> queryset;
        vector<int> ans;
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
            ans.push_back(PCSPQueryIPrune(queryset[i].first, queryset[i].second));
        }
        t2=std::chrono::high_resolution_clock::now();
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT= time_span.count();
    }
    for (int qi = 0; qi < 10; qi++){
        vector<II> queryset;
        vector<int> ans;
        pruneHoplinks = hopsize = prunepc = totlca = totpc = 0;
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
            ans.push_back(PCSPQueryIPrune(queryset[i].first, queryset[i].second));
        }
        t2=std::chrono::high_resolution_clock::now();
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT= time_span.count();
        cout << (string("q") + to_string(qi + 1)).c_str() << "Query Time\n" << runT*1000 << endl;
        setres += string("q") + to_string(qi + 1);
        setres += string(" Query Time \n") + to_string(runT*1000) + string("\n");
#ifdef showstat
        cout << "Prune #Hoplinks " << pruneHoplinks << endl;
        cout << "Prune #PC " << prunepc << " over " << totpc << endl;
        setres += string("Prune #Hoplinks ") + to_string(pruneHoplinks) + ("\n");
        setres += string("Prune #PC ") + to_string(prunepc) + string(" over") + to_string(totpc) + string("\n");
        cout << "# of Hoplinks " << hopsize <<endl;
#endif
        setres += string("# of Hoplinks ") + to_string(hopsize) + string("\n");

        FILE *fp_out = fopen((prefix + sfile + string("q") + to_string(qi + 1) + string("PCSPResults")).c_str(), "w");
        for (int i = 0; i < ans.size(); i++)
            fprintf(fp_out, "%f\n", ans[i]);
        fclose(fp_out);
        setres += string("\n");
    }

    FILE *fp_record = fopen("PCSPRecord.txt", "a");
    fprintf(fp_record, "%s %s %s\n", sfile.c_str(),regL.c_str(), srandom.c_str());
    fprintf(fp_record, "%s\n", setres.c_str());
    fclose(fp_record);
    return 0;
}
