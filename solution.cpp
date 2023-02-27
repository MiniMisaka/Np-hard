/*
My solution consists of three steps.

The first stage is finding some kind of answer in a greedy way.
Initially, all k sets are empty. I randomly iterate over all vertices from 1 to n. 
And for each vertex I look for a component with the maximum number of adjacent vertices and add a vertex to that component. 
After I typed the answer, I save it.

The second stage consists of improving the answer in the following way. 
For each vertex i from 1 to n, I look for vertex j also from 1 to n, which maximizes the answer after exchanging the components of these vertices. 
After that, from each component from 1 to k, I remove the vertices that have the minimum number of adjacent edges in the component. 
That is, I have k vertices without components and k components, and I need to pair them in such a way as to maximize the answer. 
And this problem is solved by the Hungarian algorithm in O(k^3) time.
I repeat the second step until my answer gets better, and if my current answer is better I update it.

At the third stage, I have an answer that I can't improve, because of this, depending on n / k, I swap the components of random vertices. 
If n/k>300 I do it 80 times, otherwise if n/k>100 I change them 50 times, and in all other cases 10 times.
Then I return to the second stage. And I do all this while the code runs for less than 2.9 seconds

*/

#pragma GCC optimize("Ofast") 

#include <bits/stdc++.h>                                                               
#define ll long long
#define ull unsigned long long
#define ld long double
#define sz(a) (int)a.size()
#define fi first
#define se second
#define all(x) x.begin(),x.end()
#define pb push_back  
#define mp(a, b) make_pair(a, b)
 
using namespace std;


typedef pair < int , int > pii ;                                            
typedef pair < long long  , long long > pll ;


const int N = 1e3 + 5, K1 = 111537;


int n, m, k;
vector < int > gr[N], rgr[N];

bool g[N][N];

int bestScore = 1e9;
vector < int > ans(n + 1);
int mxdelta = 0;
int upd(vector<int>&cur){
	int score = 0;
	for(int i = 1; i <= n; i++){
		for(int x: gr[i]){
			score += (x < i && cur[x] != cur[i]);	
		}
	}
	if(score < bestScore){
		bestScore = score;
		ans = cur;
	}
	return m-score;
}
void vengerka(vector < vector<int> > &c, vector < int > &curAns, int n, int m, vector < int >&del, int &W){ //implementation of the Hungarian algorithm
	vector<int> u (n+1), v (m+1), p (m+1), way (m+1);

	int INF = 1e9;

	for (int i=1; i<=n; ++i) {
		p[0] = i;
		int j0 = 0;
		vector<int> minv (m+1, INF);
		vector<bool> used (m+1, false);
		do {
			used[j0] = true;
			int i0 = p[j0],  delta = INF,  j1;
			for (int j=1; j<=m; ++j)
				if (!used[j]) {
					int cur = -c[i0][del[j]]-u[i0]-v[j];
					if (cur < minv[j])
						minv[j] = cur,  way[j] = j0;
					if (minv[j] < delta)
						delta = minv[j],  j1 = j;
				}
			for (int j=0; j<=m; ++j)
				if (used[j])
					u[p[j]] += delta,  v[j] -= delta;
				else
					minv[j] -= delta;
			j0 = j1;
		} while (p[j0] != 0);
		do {
			int j1 = way[j0];
			p[j0] = p[j1];
			j0 = j1;
		} while (j0);
	}
	vector < int > res(n + 1);

	for (int j=1; j<=m; ++j){
		res[p[j]] = j;
	}
	vector < bool > deleted(m + 1);
	for(int i = 1; i <= n; i++){
		int u = del[res[i]];    // add component i the vertex u
		W += c[i][u];

		for(int to: gr[u])
			c[i][to]++;
		curAns[u] = i;
		deleted[res[i]] = 1; 
	}
	/*
	in one of my old solutions, I removed lm * k vertices, where lm could be greater than 1. 
	Because of this, I wrote recursively until we add back all the vertices
	but in my last solutions it is not needed
	*/
	vector < int > tmp;      
	for(int i = 0; i < sz(del); i++){
		if(!deleted[i])
			tmp.pb(del[i]);
	}
	del = tmp;
	if(sz(del) != 1)
		vengerka(c, curAns, n, m - n, del, W);
		
	
}
void upgrade(vector < int > &curAns, vector < vector<int> > &c, int W = -1){ // W is current score. if its value is -1 then it has not been calculated yet
	while(1.0 * clock()/CLOCKS_PER_SEC < 2.9){
		//start of the second stage
		while(true){
			bool imprv = 0;   // a variable that tells whether our answer has improved
			while(true){  // while there are pairs of vertices that improve the answer after we swap their components
				int hv = 0; // a variable that answers whether there are such vertices
				for(int i = 1; i <= n; i++){	
					int best = i, delta = 0; // the best vertex to swap with vertex i, and how much will the answer increase if we do this
			        for(int j = 1; j <= n; j++){
							if(i == j)
							continue;
						if(curAns[i] == curAns[j])
							continue; // If the vertices are in the same component, then there is no point in changing them

						int id1 = curAns[i];
						int id2 = curAns[j];
						int d = -c[id1][i] + c[id2][i] + c[id1][j] - c[id2][j] - 2 * (g[i][j]); // How much will the answer change if we change these vertices

						if(d > delta) // if it is better than our current vertex, then update it
							delta = d, best = j;   
					}
					if(best == i) // if we have not found such a vertex, then we go further
						continue;
					
					if(W != -1) // if W is known then increase it by + delta
						W += delta;
		            // Changing the cost array and swap the vertex components "best" and i
					for(int to:gr[i])
					    c[curAns[i]][to]--;		
					for(int to:gr[best])
					    c[curAns[best]][to]--;		
			
					swap(curAns[i], curAns[best]);
			
					for(int to:gr[i])
					    c[curAns[i]][to]++;		
					for(int to:gr[best])
					    c[curAns[best]][to]++;		
					hv = 1; // we have found at least one pair with a positive delta
				}
				if(!hv)break; // if there's no such pair of vertexes we cant improve it 
	    	}
			if(W == -1)  //if W is unknown we make it known 
			   W = upd(curAns);     
			else if(W > m - bestScore){   // try to make answer better
				imprv = 1;  // our answer is imporved 
				ans = curAns;	
				bestScore = m - W;
			}

			vector < vector < pii > > grp(k + 1); // for each component we will store its vertices and the cost of this vertex in this component

			for(int i = 1; i <= n; i++){
				grp[curAns[i]].pb({c[curAns[i]][i],i});
			}
			if(k <= 500){   // prepare for Hungarian algorithm. if k > 500 there's no meaning of this algorithm
				int lm = 1; // how many vertices we will take from each component
			    vector < int > del; // deleted vertices 
				
				for(int i = 1; i <= k; i++){
					// we add to del vertices with minimum cost 
					sort(all(grp[i]));      
					reverse(all(grp[i]));
					for(int x = 0; x < lm;x++){
						del.pb(grp[i].back().se),grp[i].pop_back();
					}
				}
			    for(int i: del){ // removing vertices from components
			    	W -= c[curAns[i]][i];
			    	for(int x: gr[i])
			    		c[curAns[i]][x]--;
			    	curAns[i] = 0;
			    }
				//making our array 1-indexed			    
			    del.pb(0); 
			    reverse(all(del));
				// start of Hungarian algorithm 			    
			    vengerka(c, curAns, k, lm * k, del, W);
				
				if(W > m - bestScore){// try to make answer better
					imprv = 1;  // our answer is imporved 
					ans = curAns;	
					bestScore = m - W;
				}
	        }
	        if(!imprv) // we can't improve the answer
	        	break;
        }
		if(true){// 3 stage
			vector < vector < pii > > grp(k + 1);// for each component we will store its vertices and the cost of this vertex in this component

			for(int i = 1; i <= n; i++){
				grp[curAns[i]].pb({c[curAns[i]][i],i});
			}

            for(int i = 0; i < (n/k>300?80:(n/k>100?50:10)); ){
		        //generation of two vertices
		    	int id1 = rand()%k + 1; 
		    	int id2 = rand()%k + 1;
		    	int x = grp[id1][rand()%sz(grp[id1])].se;
				int y = grp[id2][rand()%sz(grp[id2])].se;
				if(curAns[x] == curAns[y]) // if they are in the same component then it makes no sense to change them
					continue;
				i++;
				// change the components of two vertices				
				W -= c[curAns[x]][x];
				W -= c[curAns[y]][y];
		
				for(int to:gr[x])
			    	c[curAns[x]][to]--;		
				for(int to:gr[y])
				    c[curAns[y]][to]--;		
				swap(curAns[x], curAns[y]);
			
				for(int to:gr[x])
				    c[curAns[x]][to]++;		
				for(int to:gr[y])
				    c[curAns[y]][to]++;		
				W += c[curAns[x]][x];
				W += c[curAns[y]][y];
		    }
	    }
    }
}



void groupByGroup(){ //first stage
	vector < int > order;

	for(int i = 1; i <= n; i++)
		order.pb(i);
	
	random_shuffle(all(order));
	// generate random vertex order
	int len = n / k;     // minimum size of each component
	int big = n % k;	//the number of components whose size should be one vertex larger
	
	vector < int > curAns(n + 1), Sz(n + 1); // current anwer and size of each component 
	// A two-dimensional costarray that stores the number of adjacent vertices for each vertex of the component	 
	// c[i][j] - this is essentially how much the answer will increase if we add vertex j to the component i.
	vector < vector<int> > c(k + 1, vector < int > (n + 1));                                               
	 
	
	for(int i : order){ // iterate over of all vertices 
		int p = 0; // index of the best component, initially equal to 0
		for(int j = 1; j <= k; j++){
			if(Sz[j] == len + 1 or (Sz[j] == len and big == 0)) //If the component has reached its maximum size, then I skip it
				continue;

			if(c[j][i] >= c[p][i]) // if component j better than component p update it
				p = j;		
		}
		curAns[i] = p; // setting that vertex i in component p
		Sz[p]++; // increasing size of component p
		big -= (Sz[p] == (len + 1)); // if component  reaches size of len + 1, the number of available big components will become one less
        for(int to: gr[i]) // I update the cost of each vertex in component number p, after adding vertex i
			c[p][to]++;
	}

	upd(curAns);  // update current answer 
	
	upgrade(curAns, c); // use the current answer and go to the second stage
}

main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    //input 
	cin >> n >> m >> k;

	for(int i = 1; i <= m; i++){
		int u, v;
		cin >> u >> v;
		gr[u].pb(v);            
		gr[v].pb(u);
		g[u][v] = g[v][u] = 1;
	}

	//start of the first stage
    groupByGroup();



	ld x = 2.0/(1 + 1.0 * bestScore / m);
	cerr << setprecision(3) << fixed << bestScore << ' ' << (125000.0 * x * x * x) << '\n';

	for(int i = 1; i <= n; i++){
		cout << ans[i] << ' ';
		if(ans[i] == 0){cerr<< i;assert(0);};
	}
}
