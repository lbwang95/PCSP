#include "Regex2MinDFA.h"
#include<bits/stdc++.h>
#include<unordered_map>
using namespace std;
#define eps 1e-8
typedef pair<double, int> DI;
typedef pair<int, int> II;
typedef unordered_map<int, double> UID;
typedef unordered_map<int, UID> UIID;
typedef unordered_map<int, int> UII;
typedef unordered_map<int, UII> UIII;
typedef pair<double, UID> DUID;
typedef pair<double, II> DII;
typedef pair<int, UIID> IV;
typedef long long ll;
const int MAX_V = 6262106;
int N, M;//# of vertices and edges
double optw = DBL_MAX;//optimal answer

struct edge{
    int from, to;
    double weight;
    char label;
    edge(){}
    edge(int a,int b,double w,char l){
        from = a, to = b, weight = w, label = l;
    }
};
unordered_map<int, edge> adj[MAX_V];//contains only edges to higher rank
unordered_map<int,int> adjo[MAX_V], adjT[MAX_V];//contains all the edges
DFA minDfa;
void Reg2minDFA(string str1){
	//string str = "(a|b)*abb";
	//string str = "(a|b)*c|z*";
    string oristr = "";
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
	
	NFA n = strToNfa(str);
	//printNFA(n);
	DFA d = nfaToDfa(n, str);
	//printDFA(d);
	minDfa = minDFA(d);
	printMinDFA(minDfa);
    string teststr = "bbbpppppp";
    printf("%s: %d DFA states\n", oristr.c_str(), minDfaStateNum);
    printf("%s test:%d\n", teststr.c_str(), indicator(minDfa, teststr));
}

double df[MAX_V][MAX_NS], db[MAX_V][MAX_NS];
int rtrans[MAX_NS][26];
double DijkstraQuery(int s, int t){
	//use bidirectional search to speed up
    optw = DBL_MAX;
    if (s == t)
        return 0;
    s--, t--;
    priority_queue<DII, vector<DII>, greater<DII>> Qf, Qb;
    UIII sf, sb;
    for (int i = 0; i <= N;i++){
        for (int j = 0; j < minDfaStateNum;j++){
            df[i][j] = db[i][j] = DBL_MAX;
            if (i == t && finalFlag[j]){
                db[i][j] = 0;
                sb[i][j] = 1;
                Qb.push(DII(0, II(t, j)));
            }
        }
    }
    df[s][minDfa.startState] = 0;
    sf[s][minDfa.startState] = 1;
    Qf.push(DII(0, II(s, minDfa.startState)));
    double mu = DBL_MAX;
    while (!Qf.empty() && !Qb.empty()){
        while(df[Qf.top().second.first][Qf.top().second.second]<Qf.top().first)
            Qf.pop();
        while(db[Qb.top().second.first][Qb.top().second.second]<Qb.top().first)
            Qb.pop();
        DII qfu = Qf.top(), qfv = Qb.top();
        int u = qfu.second.first, v = qfv.second.first;
        int qu = qfu.second.second, qv = qfv.second.second;
        Qf.pop();
        Qb.pop();
        sf[u][qu] = 1;
        sb[v][qv] = 1;
        //printf("(%d %d %f) (%d %d %f)\n", u + 1, qu, qfu.first, v + 1, qv, qfv.first);
        unordered_map<int, edge>::iterator it;
        for (it = adj[u].begin(); it != adj[u].end();it++){
            int to = it->first;
            edge e = it->second;
            int toq = minDfa.trans[qu][e.label - 'a'];
            if (toq == -1)
                continue;
            if (df[to][toq] > df[u][qu] + e.weight){
                df[to][toq] = df[u][qu] + e.weight;
                Qf.push(DII(df[to][toq], II(to, toq)));
            }
            if (sb.count(to) && sb[to].count(toq)&&df[to][toq]+db[to][toq]<mu){
                mu = df[to][toq]+db[to][toq];
            }
        }
        for (it = adj[v].begin(); it != adj[v].end();it++){
            int to = it->first;
            edge e = it->second;
            int toq = rtrans[qv][e.label - 'a'];
            if (toq == -1)
                continue;
            if (db[to][toq] > db[v][qv] + e.weight){
                db[to][toq] = db[v][qv] + e.weight;
                Qb.push(DII(db[to][toq], II(to, toq)));
            }
            if (sf.count(to) && sf[to].count(toq)&&df[to][toq]+db[to][toq]<mu)
                mu = df[to][toq]+db[to][toq];
        }
        if (df[u][qu] + db[v][qv] > mu)
            break;
    }
    optw = mu;
    //printf("%f\n", optw);
    if(optw==DBL_MAX)
        optw = -1;
    return optw;
}

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
            adj[u][v] = edge(u, v, w, l);
            adj[v][u] = edge(u, v, w, l);
        }
    }
    Reg2minDFA(regL);
    cout << endl;
    std::chrono::high_resolution_clock::time_point t1, t2;
	std::chrono::duration<double> time_span;
	double runT;
    
    for (int i = 0; i < MAX_NS; i++){
        for (int j = 0; j < 26;j++){
            rtrans[i][j] = -1;
            int toS = minDfa.trans[i][j];
            if(toS != -1){
                rtrans[toS][j] = i;
            }
        }
    }

    string setres;
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
            ans.push_back(DijkstraQuery(queryset[i].first, queryset[i].second));
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
        for (int i = 0; i < queryset.size(); i++){
            ans.push_back(DijkstraQuery(queryset[i].first, queryset[i].second));
        }
        t2=std::chrono::high_resolution_clock::now();
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT= time_span.count();
        cout << (string("q") + to_string(qi + 1)).c_str() << "Query Time\n" << runT*1000 << endl;
        setres += string("q") + to_string(qi + 1);
        setres += string(" Query Time \n") + to_string(runT*1000) + string("\n");

        FILE *fp_out = fopen((prefix + sfile + string("q") + to_string(qi + 1) + string("DijkstraResults")).c_str(), "w");
        for (int i = 0; i < ans.size(); i++){
            fprintf(fp_out, "%f\n", ans[i]);
        }
        fclose(fp_out);
        setres += string("\n");
    }

    FILE *fp_record = fopen("DijkstraRecord.txt", "a");
    fprintf(fp_record, "%s %s\n", sfile.c_str(),regL.c_str());
    fprintf(fp_record, "%s\n", setres.c_str());
    fclose(fp_record);
    return 0;
}
