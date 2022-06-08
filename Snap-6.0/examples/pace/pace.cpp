#include "stdafx.h"
#include <iostream> 
#include <vector>
#include <sstream> 
#include <algorithm> 
#include <array>
#include <signal.h>
#include <cmath>
#include <unistd.h>
#include <unordered_set>
#include <map>
#include <cstdlib>
#include <set>
 
//regarder comment optimiser les parametres, avec des papiers type celui des coréens qui font du simplexe..
//voir les restarts apres un nombre de fails en reprenant la temperature du moment où la best temps et la best solution so far

//bien passer les map en adresse sinon recopie !! (voir avec classes sinon)

//Choisir les hyperparametres en fonction de l'instance ? Faire une regression sur les stats pour savoir ce qui est le mieux ? Selon n, m, dense, ... ?

//voir les papiers qui donnent des techniques pour set la temperature

//no memory done, could improve?

//impl tricks : relabel too long, saving the best too long, saving iplus and stuff, choix aleatoire et pas pondéré
//politique temperature/cooling/... a ameliorer

//faire des simulations monte carlo / nmcs pour évanluer les coups ?

//refaire du kernel pendant le recuit?

/*
During this process the input can break apart in multiple strongly connected
components, when this happens we remove the arcs that go between the com-
ponents to allow Rules 2 and 4 to trigger.
https://snap.stanford.edu/snap/doc/snapuser-ref/dc/d57/cncom_8h.html#a5c8074996326219105c7e322475a562e
*/

typedef PNGraph PGraph;  //   directed graph
typedef PUNGraph UGraph; // undirected graph
typedef PGraph::TObj::TNodeI TNodeI;

//Parameters part 2
double T0 = 0.5;
double ALPHA = 0.9;
int maxMv;
int MAX_MV_COEF = 10;
//int maxFails = 100;
int RESTARTS_LIMIT = 60;  
int MAX_RESTARTS = 100;
int LIMIT_COLD_RESTART = 10;
//int MAX_BIG_RESTARTS = 20;
float lambd = 0.3;
int MAX_MV_SAV = 100;

volatile sig_atomic_t tle = 0;
 
void term(int signum)
{
    tle = 1;
}

PGraph readGraph() {
  std::string line;
 
  std::getline(std::cin,line);
  //skip comments
  while( line[0] == '%' ) {
    std::getline(std::cin, line);
  }

  int N, M, ew;
  std::stringstream ss(line);
  ss >> N >> M >> ew;
  //Graph graph(N);
  PGraph G = PGraph::TObj::New();

  long source = 1;
  while( std::getline(std::cin, line) ) {

    if (line[0] == '%') { // a comment in the file
      continue;
    }
    std::stringstream ss(line);

    G->AddNodeUnchecked(source);
    long target;
    while( ss >> target ) {
      G->AddNodeUnchecked(target);
      G->AddEdge(source, target);
    }
    if(std::cin.eof()) {
      break;
    }
    source++;
  }
  IAssert(G->GetNodes() == N);
  IAssert(G->GetEdges() == M);
  return G;
}

bool delEdgesBetweenScc(const PGraph& G, std::vector<int>& cclabel) {
fprintf(stderr, "Computing Strong CC\n");
  //get Strong Con Comp
  TCnComV SCnComV;
  TSnap::GetSccs(G, SCnComV);
  int found = false;

  //labeling
  //int label=0;
  fprintf(stderr, "Labelling\n");
  
  for(int ccid = 0 ; ccid<SCnComV.Len() ; ccid++) {
    TCnCom cc = SCnComV[ccid];
    for(int i = 0 ; i<cc.Len() ; i++) {
      int v = cc[i];
      //fprintf(stderr, "%ld %ld %d\n", cclabel.size(), cclabel.capacity(), v);
      cclabel[v] = ccid;
    }
  }
  
  if(SCnComV.Len()>1) {
    fprintf(stderr, "May have some edges to delete\n");
    std::vector<std::pair<int, int>> todelete;
    //look for edges between StrongCC
    for(auto e = G->BegEI() ; e<G->EndEI() ; e++) {
      int u = e.GetSrcNId();
      int v = e.GetDstNId();
      if(cclabel[u] != cclabel[v]) {
        //delete
        //fprintf(stderr, "Deleting %d %d\n", u, v);
        //G->DelEdge(u, v);
        todelete.push_back(std::pair(u, v));
        found = true;
      }
    }
    for(auto e : todelete) {
      G->DelEdge(e.first, e.second);
    }
  }
  return found;
}

bool isClique(const UGraph& U, int vid) {
  auto v = U->GetNI(vid);
  for(int e1=0 ; e1<v.GetDeg() ; e1++) {
    for(int e2=e1+1 ; e2<v.GetDeg() ; e2++) {
      if(!U->IsEdge(v.GetNbrNId(e1), v.GetNbrNId(e2))) return false;
    }
  }
  return true;
}

bool isPiVertex(const PGraph& G, const UGraph& U, int vid) {
  auto v = G->GetNI(vid);
  for(int e=0 ; e<v.GetDeg() ; e++) {
    int u = v.GetNbrNId(e);
    if (!U->IsEdge(vid, u)) return false;
  }
  /*
  fprintf(stderr, "%d is a PI vertex\n", vid);
  for(int e=0 ; e<v.GetDeg() ; e++) {
    int u = v.GetNbrNId(e);
    fprintf(stderr, "neighb %d\n", u);
  }
  */
  return true;
}

bool condition1(const PGraph& G, const UGraph& U, int uid, int vid) {
  auto u = G->GetNI(uid);
  //fprintf(stderr, "checking cond 1 for (%d,%d)\n", uid, vid);
  //fprintf(stderr, "pred of %d:\n" ,vid);
  auto v = G->GetNI(vid);
  
  /*
  for(int e=0 ; e<v.GetInDeg() ; e++) {
    fprintf(stderr, "pred of v is %d\n", v.GetInNId(e));
  }
  */
  for(int e=0 ; e<u.GetInDeg() ; e++) {
    auto predU = u.GetInNId(e);
    //fprintf(stderr, "pred is %d\n", predU);
    //fprintf(stderr, "is PIE? %d\n", U->IsEdge(predU, uid));

    if(!U->IsEdge(predU, uid)) {  //predU is a non-Pi-Pred
      //must be also a pred of v
      //fprintf(stderr, "is? %d\n", G->IsEdge(predU, vid));
      if(!G->IsEdge(predU, vid)) {
        return false; //some of Pu is not in Pv
      }
    }
  }
  //fprintf(stderr, "true\n");
  return true;
}

bool condition2(const PGraph& G, const UGraph& U, int uid, int vid) {
  auto v = G->GetNI(vid);
  for(int e=0 ; e<v.GetOutDeg() ; e++) {
    auto succV = v.GetOutNId(e);
    if(!U->IsEdge(vid, succV)) {  //succV is a non-Pi-Succ
      //must be also a succ of u
      if(!G->IsEdge(uid, succV)) {
        return false; //some of Sv is not in Su
      }
    }
  }
  return true;
}

std::vector<int> reduction(const PGraph& G) {
  std::vector<int> sol;
  bool reduced = true;
  //before the reduction to avoid labels problems!
  std::vector<int> cclabel; //in which cc is each vertex
  cclabel.reserve(G->GetNodes()+1);

  while(reduced) {
    reduced = false;
    std::vector<int> toRemove;
    fprintf(stderr, "n,m:%d %d\n", G->GetNodes(), G->GetEdges());

    for (auto v = G->BegNI(); v < G->EndNI(); v++) {
      //printf("%d\n", v.GetId());

      if(v.GetInDeg() == 0 || v.GetOutDeg() == 0) {
        //G->DelNode(v.GetId());
        toRemove.push_back(v.GetId());
        reduced = true;
      } 
      else if (v.GetInDeg() == 1 && !G->IsEdge(v.GetId(), v.GetId())) {
        auto u = v.GetInNId(0);  //only one
        for (int e = 0; e < v.GetOutDeg(); e++) {  
          G->AddEdge(u, v.GetOutNId(e));
        }
        toRemove.push_back(v.GetId());
        reduced = true;
      }
      else if (v.GetOutDeg() == 1 && !G->IsEdge(v.GetId(), v.GetId())) {
        auto u = v.GetOutNId(0);  //only one
        for (int e = 0; e < v.GetInDeg(); e++) {  
          G->AddEdge(v.GetInNId(e), u);
        }
        toRemove.push_back(v.GetId());
        reduced = true;
      }
      //forced in solution
      else if (G->IsEdge(v.GetId(), v.GetId())) {
        toRemove.push_back(v.GetId());
        sol.push_back(v.GetId());
        reduced = true;
      }
      
    }
    for(auto v : toRemove) {
      G->DelNode(v);
    }

    //PIE
    if(!reduced) {  //at the last moment, check if there are edges between SCC we can delete
      //check for PIE edges
      std::vector<std::pair<int,int>> pie;

      //UGraph U = UGraph::TObj::New();

      for(auto e = G->BegEI() ; e<G->EndEI() ; e++) {
        int u = e.GetSrcNId();
        int v = e.GetDstNId();
        if (u<v && G->IsEdge(v, u)) {
          pie.push_back(std::pair(u,v));
          pie.push_back(std::pair(v,u));
/*
          U->AddNodeUnchecked(u);
          U->AddNodeUnchecked(v);
          U->AddEdge(u, v);
*/
        }
      }
      fprintf(stderr, "Tempo deletion of %ld PIE edges\n", pie.size());
      for(auto e : pie) {
        G->DelEdge(e.first, e.second);
      }

      reduced = delEdgesBetweenScc(G, cclabel);
      //cclabel.clear();

      //put back
      for(auto e : pie) {
        G->AddEdge(e.first, e.second);
      }

      //"work" but one by one takes too much time for not much benefice?
      if(!reduced) {  //CORE
        /*
        struct degcmp {
          static PGraph G;

          bool operator() (int a, int b) const {
              TNodeI aid = G->GetNI(a);
              TNodeI bid = G->GetNI(b);
              return (aid.GetDeg() < bid.GetDeg());
            };
        };
        */
        //std::set<int, degcmp> piv;

        UGraph U = UGraph::TObj::New();

        for(auto e = G->BegEI() ; e<G->EndEI() ; e++) {
          int u = e.GetSrcNId();
          int v = e.GetDstNId();
          if (u<v && G->IsEdge(v, u)) {
            U->AddNodeUnchecked(u);
            U->AddNodeUnchecked(v);
            U->AddEdge(u, v);

          }
        }
        
        auto cmp = [&G](int a, int b) { 
            TNodeI aid = G->GetNI(a);
            TNodeI bid = G->GetNI(b);
            //need a total order for set, need to find a way to tie break
            if(aid.GetDeg() == bid.GetDeg()) {
              return a<b;
            }
            else {
              return (aid.GetDeg() < bid.GetDeg());
            }
         };
        
        std::vector<int> piv;
        for(auto v = U->BegNI() ; v<U->EndNI() ; v++) {
          piv.push_back(v.GetId());
        }
        std::sort(piv.begin() , piv.end() , cmp);
         
        //degcmp::G = G;
        //std::set<int, degcmp> piv;
        /*
        std::set<int, decltype(cmp)> piv(cmp);  //peut pas utiliser un set avec degré
        
        
        for(auto e = G->BegEI() ; e<G->EndEI() ; e++) {
          int u = e.GetSrcNId();
          int v = e.GetDstNId();
          if (u<v && G->IsEdge(v, u)) {
            piv.insert(u);
            piv.insert(v);
          }
        }
        */
        /*
        std::vector<int> piv;
        for(auto v = G->BegNI() ; v<G->EndNI ; v++) {
          for(int e = 0 ; e<v.GetOutDeg() ; e++) {
            //vector + unorderned map ? or ..
          }
        }
        */
        std::unordered_set<int> invalid;
        std::vector<int> todel;
        for(auto v : piv) { //piv in ascending degree
          //fprintf(stderr, "piv %d deg %d\n", v, G->GetNI(v).GetDeg());
          if (G->IsNode(v) && (invalid.find(v) == invalid.end())) { //not present
            //check if v and N(v) forms a clique
            if (isPiVertex(G, U, v) && isClique(U, v)) {
              fprintf(stderr, "Found a clique on PI-vertex %d\n", v);
              //decallage ID entre U et G ?
              auto vni = U->GetNI(v);
              //auto vni2 = G->GetNI(v);

              //fprintf(stderr, "vertex %d outdeg %d, indeg %d degree %d\n", v, vni.GetOutDeg(), vni.GetInDeg(), vni.GetDeg());
              //fprintf(stderr, "vertex %d outdeg %d, indeg %d\n", v, vni2.GetOutDeg(), vni2.GetInDeg());
              int iniDeg = vni.GetDeg();
              for(int e=0 ; e<iniDeg ; e++) {
                //fprintf(stderr, "%d deletion + FVS of %d\n", e, vni.GetNbrNId(e));

                sol.push_back(vni.GetNbrNId(e));
                //G->DelNode(vni.GetNbrNId(e));
                //U->DelNode(vni.GetNbrNId(e));
                todel.push_back(vni.GetNbrNId(e));
              }
              //fprintf(stderr, "deletion of %d\n", v);

              //G->DelNode(v);
              //U->DelNode(v);
              todel.push_back(v);

              for(auto v : todel) {
                //fprintf(stderr, "will del %d %d\n", v, G->IsNode(v));
                G->DelNode(v);
                U->DelNode(v);
              }
              todel.clear();
              reduced = true;
              //break;
            }
            else {
              //invalid v and its neigbors
              invalid.insert(v);
              auto vni = U->GetNI(v);
              for(int e=0 ; e<vni.GetDeg() ; e++) {
                invalid.insert(vni.GetNbrNId(e));
              }
            }
          }
        }
        
        if(!reduced) {  //DOME
          //pb que faire si que des PIE edges : ca devrait sauter!
          std::vector<std::pair<int, int>> todelete;
          for(auto e=G->BegEI() ; e<G->EndEI() ; e++) {
            //check if e is dominated
            int u = e.GetSrcNId();
            int v = e.GetDstNId();
            if(!U->IsEdge(u, v) && (condition1(G, U, u, v) || condition2(G, U, u, v))) {
            //if(condition1(G, U, u, v)) {
              todelete.push_back(std::pair(u, v));
              reduced = true;
            }
          }
          if (todelete.size() > 0) {
            fprintf(stderr, "Found some dominated edges %ld!\n", todelete.size());
          }
          for(auto e : todelete) {
            G->DelEdge(e.first, e.second);
          }
        }
        
      }
    }
  }
  return sol;
}


bool canBeAddInTopol(const PGraph& G, const std::vector<double>& S, TNodeI v) {
  for(int e = 0 ; e<v.GetOutDeg() ; e++) {
    if(S[v.GetOutNId(e)] != -1) return false;
  }
  return true;
}

void initialTopSort(const PGraph& G, std::vector<double>& S) {
  //TODO tenter ignorer le gros degrés du debut pour les gros graphes denses ?
  //pas sur,la 119 est merdique mais pas de gros degrés pour autant
  std::vector<TNodeI> nodes;
  nodes.reserve(G->GetNodes());
  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    nodes.push_back(v);
  }
  
  //fprintf(stderr, "Add done\n");
  
  std::sort(nodes.begin(), nodes.end(), [](TNodeI a, TNodeI b) {
        return (a.GetInDeg()-a.GetOutDeg()) < (b.GetInDeg()-b.GetOutDeg());
    });
  //must be ascending  
  //fprintf(stderr, "Sort done\n");
  /*
  for(auto v : nodes)
    std::cout << v.GetId() << ' ' << v.GetInDeg() << ' ' << v.GetOutDeg() << std::endl;
  */
  int label = 1;

  for(auto v : nodes) {
    //printf("%d ", v.GetId());
    if (canBeAddInTopol(G, S, v)) {
      S[v.GetId()] = label;
      label++;
      //printf("%d %d\n", label, nodes.size());
    }
  }
  //fprintf(stderr, "Labeling done\n");
}

long int sizeDFVS(const PGraph& G, const std::vector<double>& S) {
  long int size = 0;
  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    if(S[v.GetId()] == -1) size++;
  }
  return size;
}

int popRandom(std::vector<int>& vector) {
  //get a random element
  //TODO use a better random generator ?
  int idx = rand()%vector.size();
  auto elt = vector[idx];
  std::swap(vector[idx], vector.back());
  vector.pop_back();
  return elt;

  //swap with the last
  //remove last
}

int popSampled(std::vector<int>& candidates, const std::vector<double>& probas) {
  double sum = 0;
  for(int i=1 ; i<candidates.size() ; i++) {
    auto v = candidates[i];
    sum += probas[v];
  }
  double stop = (rand () / (RAND_MAX + 1.0)) * sum;
  //printf("Sum = %f, Stop : %f\n", sum, stop);
  sum = 0;
  for(int i=1 ; i<candidates.size() ; i++) {
    auto elt = candidates[i];
    sum += probas[elt];
    if (sum >= stop) {
      std::swap(candidates[i], candidates.back());
      candidates.pop_back();
      return elt;
    }
  }
  IAssert(1!=1);  //shouldn't be here
  return 0; 
}

int iplus(const PGraph& G, const std::vector<double>& S, int v) {
  auto node = G->GetNI(v);
//  if(node.GetOutDeg() > 0) {
//    int min = std::numeric_limits<int>::max();
    //int min = SvalInt + 1; //TODO to check
    int min = G->GetNodes()+1;
    for(int e=0 ; e<node.GetOutDeg() ; e++) {
      int idtop = S[node.GetOutNId(e)];
      if (idtop != -1 && idtop < min) {
        min = idtop;
      }
    }
    return min;
//  } 
//  else {
//    return SvalInt + 1;
//  } 
}

int iminus(const PGraph& G, const std::vector<double>& S, int v) {
  int max = 0;
  auto node = G->GetNI(v);

  for(int e=0 ; e<node.GetInDeg() ; e++) {
    int idtop = S[node.GetInNId(e)];
    if (idtop != -1 && idtop > max) {
      max = idtop;
    }
  }
  return max+1;
}

std::vector<int> CVminus(const PGraph& G, const std::vector<double>& S, int v, int i) {
  std::vector<int> sol;
  auto node = G->GetNI(v);
  //sol.reserve(node.GetInDeg()); //maybe too much, but avoid realloc?
  for(int e=0 ; e<node.GetInDeg() ; e++) {
    auto j = node.GetInNId(e);
    if (S[j] != -1 && S[j]>=i) {
      sol.push_back(j);
    }
  }
  return sol;
}

std::vector<int> CVplus(const PGraph& G, const std::vector<double>& S, int v, int i) {
  std::vector<int> sol;
  auto node = G->GetNI(v);
  //sol.reserve(node.GetOutDeg());  //maybe too much but avoid realloc?
  for(int e=0 ; e<node.GetOutDeg() ; e++) {
    auto j = node.GetOutNId(e);
    if (S[j] != -1 && S[j]<i) {
      sol.push_back(j);
    }
  }
  return sol;
}

int delta(const PGraph& G, const std::vector<double>& S, int v, int i) {
  return -1 + CVplus(G, S, v, i).size() + CVminus(G, S, v, i).size();
}

void updateVertex(const PGraph& G, const std::vector<double>& S, int v, int* deltasplus, int* deltasminus, std::vector<bool>& ok) {
  deltasplus[v] = delta(G, S, v, iplus(G, S, v));
  deltasminus[v] = delta(G, S, v, iminus(G, S, v));
  ok[v] = true;
}

void relabel(const PGraph& G, std::vector<double>& S) {
  //TODO pas besoin de trier si selectedS est trié ?
  //TODO pas relabel si rien a changé ?!

  std::map<double, int> selectedS;

  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    if(S[v.GetId()] != -1){
      selectedS.insert({S[v.GetId()], v.GetId()}); 
    }
  }

  int label = 1;
  //map label -> vertex

        
  
  /*
  printf("pas trié:\n");
  for(auto n : selectedS) {
    printf("%f %d\n", n.first, n.second);
  }
  printf("-------------\n");
  */
  //https://stackoverflow.com/questions/38164274/c-modifying-key-for-all-map-elements
  std::map<double, int> modifiedS;
  for(auto it = selectedS.begin() ; it != selectedS.end() ;) {
    S[it->second] = label;  
    auto nh = selectedS.extract(it++);
    nh.key() = label;
    label++;
    modifiedS.insert(modifiedS.end(), std::move(nh));   //should be O(1) given the hint
    /*
    modifiedS.insert(modifiedS.end(), {label, it->second});
    label++;
    it++;
    */
  }
  modifiedS.swap(selectedS);
  
  /*
  for(auto n : selectedS) {
    S[n.second] = label;
    //pb, on modifie les keys..
    selectedS[n.first] = label;
    label++;
  }
  */
  /*
  for(auto it = selectedS.begin() ; it != selectedS.end() ; it++) {
    if(label != it->first) {
      auto nodehandler = selectedS.extract(it);
      nodehandler.key() = label;
      selectedS.insert(std::move(nodehandler));
      label++;
    }
  }
  */

  /* //ok works
  std::map<float,int> newS;
  for (auto n : selectedS) {
    newS.insert({label, n.second});
    S[n.second] = label;  
    label++;
  }
  std::swap(newS, selectedS);
  */

  /*
  printf("-- apres :\n");
  for(auto n : selectedS) {
    printf("%f %d\n", n.first, n.second);
  }
  */
  //TODO essayer d'eviter d'avoir a recopier !
  //printf("-fin tri\n");

}

void applymove(const PGraph& G, std::vector<double>& S, int v, int b, std::vector<int>& candidates, std::vector<bool>& ok) {
  //printf("apply move on %d, %d \n", v, b);
  //S[v] = b-0.1;
  S[v] = b-0.001;  //TODO smaller
  //TODO : enlever un pourcentage de l'ecart plutot !
  //TODO if passe en dessous (! test d'egalité) relabel?
  //selectedS.insert({S[v], v});
  //v in candidates allready removed
  for(auto i : CVplus(G, S, v, b)) {
    //selectedS.erase(S[i]);  //il faut supprimer la clef qui est l'indice dans le topo !
    S[i] = -1;
    candidates.push_back(i);
    ok[i] = false;
    auto iid = G->GetNI(i);
    for(int e=0 ; e<iid.GetOutDeg() ; e++) {
      ok[iid.GetOutNId(e)] = false;
    }
    for(int e=0 ; e<iid.GetInDeg() ; e++) {
      ok[iid.GetInNId(e)] = false;
    }
  }
  for(auto i : CVminus(G, S, v, b)) { 
    //selectedS.erase(S[i]);
    
    //printf("erase %d\n", i);
    S[i] = -1;
    
    candidates.push_back(i);
    ok[i] = false;
    auto iid = G->GetNI(i);
    for(int e=0 ; e<iid.GetOutDeg() ; e++) {
      ok[iid.GetOutNId(e)] = false;
    }
    for(int e=0 ; e<iid.GetInDeg() ; e++) {
      ok[iid.GetInNId(e)] = false;
    }
  }
  ok[v] = false;
  auto vid = G->GetNI(v);
  for(int e = 0 ; e<vid.GetOutDeg() ; e++) {
    ok[vid.GetOutNId(e)] = false;
  }
  for(int e = 0 ; e<vid.GetInDeg() ; e++) {
    ok[vid.GetInNId(e)] = false;
  }

  if (S[v] - 0.001 < floor(S[v])) {
    fprintf(stderr, "Too much small steps %f for vertex %d, relabel...\n", S[v], v);
    relabel(G, S);
  }

  //relabel(G, S, selectedS);
}

float RandomBetween(float smallNumber, float bigNumber)
{
    float diff = bigNumber - smallNumber;
    return (((float) rand() / RAND_MAX) * diff) + smallNumber;
}



std::vector<double> recuit(const PGraph& G, std::vector<double>& S, int* deltasplus, int* deltasminus, std::vector<bool>& ok) {
//std::vector<double> recuit(const PGraph& G, std::vector<double>& S, int* deltasplus, int* deltasminus, std::vector<bool>& ok, std::vector<double>& probas) {
  double T = T0;
  int nbFails = 0;
  //TODO voir comment eviter les double !
  std::vector<double> Sstar(S);
  double Tstar = T0;
  //std::unordered_set<int> candidates;
  std::vector<int> candidates;  //list of candidates to get random
  //std::unordered_set<int> selectedS;  //TODO useful?
  //comparer avec un treeset ?
  //std::map<double, int> selectedS;
  int SvalInt=0;  //TODO c'est le dfvs size !!!!
  int nbRestarts = 0;
  int movesSinceSav = 0;

  candidates.reserve(G->GetNodes());  //certainly too much

  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    if(S[v.GetId()] == -1){
      candidates.push_back(v.GetId());
      SvalInt++;

    } 
    /* 
    else {
      selectedS.insert({S[v.GetId()], v.GetId()}); 
    }
    */
  }
  int Sstarval = SvalInt;

  //while(nbFails<maxFails && !tle) {
  while(!tle && nbRestarts < MAX_RESTARTS) {
    int nbMv = 0;
    bool fail = true;
    //fprintf(stderr, "Temp is now %f\n", T);

    while (nbMv < maxMv && !tle) {
      auto v = popRandom(candidates);
      //auto v = popSampled(candidates, probas);
      int b;
      int Delta;
      movesSinceSav++;

      if (!ok[v]) {
        updateVertex(G, S, v, deltasplus, deltasminus, ok);
      }

      
      if(rand()%2==0) { //+
        b = iplus(G, S, v);
        Delta = deltasplus[v];
      }
      else {
        b = iminus(G, S, v);
        Delta = deltasminus[v];
      }
      
      /*  //less good.
      auto DeltaP = deltasplus[v];
      auto DeltaM = deltasminus[v];
      if (DeltaP > DeltaM) {
        b = iminus(G, S, v);
        Delta = DeltaM;
      }
      else if (DeltaM > DeltaP) {
        b = iplus(G, S, v);
        Delta = DeltaP;
      }
      else {
      if(rand()%2==0) { //+
        b = iplus(G, S, v);
        Delta = DeltaP;
      }
      else {
        b = iminus(G, S, v);
        Delta = DeltaM;
      }
      }
      */
      if (Delta <=0 || exp(-Delta/T) >= ((double) rand() / (RAND_MAX))) {
        applymove(G, S, v, b, candidates, ok);
        SvalInt += Delta;
        nbMv++;
        //if(nbMv % 10000 == 0)
        //  fprintf(stderr, "DFVS size %d\n", SvalInt);
        //to avoid copy of the best solution, we do it only if we didn't save for a while (or if the solution is small, meaning that we will not recopy a lot anymore)
        //TODO : faire un truc qui sauvegarde moins au debut et plus à la fin... (selon la taille depart)
        if (SvalInt < Sstarval && (SvalInt < 10000 || movesSinceSav >= MAX_MV_SAV)) { //best so far
          if(SvalInt % 1000 == 0) 
            fprintf(stderr, "DFVS size %d\n", SvalInt);
          //fprintf(stderr, "real size ?%ld\n", sizeDFVS(G, S));
          //save the best
          movesSinceSav = 0;
          Sstar.assign(S.begin(), S.end());     //spend a lot of time here!! sauvegarder qu'apres un certain nombre de moves?
          Sstarval = SvalInt;
          Tstar = T;
          fail = false;
          nbRestarts = 0;
          /*
          printf("\nSstar:\n");
          for (auto v:Sstar) {
            printf("%.0f ", v);
          }
          printf("\n");
          */
          if (SvalInt == 0) {
            fprintf(stderr, "Opti !\n");
            return Sstar;
          }
        }
      } 
      else {
        //v is now again a candidate, it wasn't choose
        candidates.push_back(v);
      }
    }
    T = T*ALPHA;
    //printf("Temp is now %f\n", T);
    if (fail) {
      nbFails++;
      //fprintf(stderr, "Fail %d, current sol is %d\n", nbFails, SvalInt);
      if (nbFails == RESTARTS_LIMIT || T < 0.01) {
        fprintf(stderr, "Too much fails or temp %f too small, restart with the previous best %d at temp %f\n", T, Sstarval, Tstar);
        //restart with the current best instead of deeping..
        nbFails = 0;
        nbRestarts++;
        //T = Tstar;
        //T = Tstar + 0.1;
        T = std::min(std::max(0.2, Tstar + RandomBetween(-0.1, 0.6)), 0.9);
        //ALPHA = 0.9;
        //ALPHA -= 0.1;
        //ALPHA = std::min(std::max(0.5, ALPHA + RandomBetween(-0.2, 0.2)), 0.99);

        MAX_MV_COEF = std::min(std::max(7, MAX_MV_COEF + int(RandomBetween(-10,10))), 80);
        maxMv = MAX_MV_COEF*G->GetNodes();


        fprintf(stderr, "Temp is now %f with ALPHA %f and MAXMV %d\n", T, ALPHA, MAX_MV_COEF);
        //T = T0;
        S.clear();

        //TODO here add only some parts?
        S.assign(Sstar.begin(), Sstar.end());
        SvalInt = Sstarval;
        
        //SvalInt = 0;

        //update candidates and selecteed!
        candidates.clear();
        //selectedS.clear();
        //data is not reliable anymore
        std::fill(ok.begin(), ok.end(), false);

        /*
        if(nbRestarts >= LIMIT_COLD_RESTART) {
          fprintf(stderr, "Cold restart !\n");
          SvalInt = 0;
          for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
            if(S[v.GetId()] == -1 ||  rand()%10>8){  //keep x% of the solution? (and add others..)
              candidates.push_back(v.GetId());
              S[v.GetId()] = -1;  //for the new ones
              SvalInt++;
            }
          }
          //nbRestarts = 0;
          fprintf(stderr, "DFVS is now %d\n", SvalInt);
        }
        else {
        */
          for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
            if(S[v.GetId()] == -1){
              candidates.push_back(v.GetId());
              //SvalInt++;
            }  
            /*
            else {
              selectedS.insert({S[v.GetId()], v.GetId()}); 
            }
            */
          }
        //}
      }
    }
    else {
      fprintf(stderr, "reloop after %d fails, nbMv %d\n", nbFails, nbMv);
      nbFails = 0;
    }
  }
  fprintf(stderr, "Too much restarts %d (or TLE), best is %d\n", nbRestarts, Sstarval);
  return Sstar;
}

void probas(const PGraph& G, std::vector<double>& probs ) {
  //std::vector<float> prob;
  //prob.push_back(0);  //no vertex 0

  //maxs
  int dm = 0;
  int dp = 0;
  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    if(v.GetInDeg() > dm) dm = v.GetInDeg();
    if(v.GetOutDeg() > dp) dp = v.GetOutDeg();
  }
  
  int m = dm + dp;

  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    //prob.push_back(m - v.GetInDeg() + v.GetOutDeg() - lambd*(std::abs(v.GetInDeg() - v.GetOutDeg())));
    probs[v.GetId()] = m - v.GetInDeg() + v.GetOutDeg() - lambd*(std::abs(v.GetInDeg() - v.GetOutDeg()));
  } 
//  return prob;
}


int main(int argc, char* argv[]) {
  struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_handler = term;
    sigaction(SIGTERM, &action, NULL);
 
    std::ios_base::sync_with_stdio(false);
 

  // this code is independent of what particular graph implementation/type we use
  fprintf(stderr, "Creating graph:\n");
  //PGraph G = PGraph::TObj::New();
  PGraph G = readGraph();
  fprintf(stderr, "Graph created.\n");

  IAssert(G->IsOk());
 

  //Parameters
  //std::srand(0);
  std::srand(time(NULL));
  //float lambd = 0.2;

  //arrays of size G+1 (since start at 1)
  int deltasplus[G->GetNodes()+1];
  int deltasminus[G->GetNodes()+1];

  std::vector<bool> ok(G->GetNodes()+1, false);
  std::vector<double> S(G->GetNodes()+1, -1);
  //std::vector<double> probs(G->GetNodes()+1, 0);

  //std::cout << ok.at(5) << ", " << deltasminus[5]+1 << S.at(10);

  fprintf(stderr, "Starting reduction rules...\n");
  std::vector<int> sol1 = reduction(G);
  fprintf(stderr, "n,m:%d %d\n", G->GetNodes(), G->GetEdges());
  return 0;
  fprintf(stderr, "Reduced vertices : %ld\n", sol1.size());
  for(auto v : sol1) {
    std::cout << v << std::endl;
  }

  if(argc == 5) {
    fprintf(stderr, "Arguments setting:\n");
    // temp ALPHA nbm
    T0 = atof(argv[1]);
    ALPHA = atof(argv[2]);
    MAX_MV_COEF = atoi(argv[3]);
    RESTARTS_LIMIT = atoi(argv[4]);
  }
  else {
    /*
    if(G->GetNodes() < 8000) {  //"small" instances
      T0 = 0.5;
      ALPHA = 0.99;
      MAX_MV_COEF = 20;     
    }
    else {      //"large" instances
      T0 = 0.3;
      ALPHA = 0.9;
      MAX_MV_COEF = 5;
    }*/
    int n = G->GetNodes();
    int m = G->GetEdges();
    double density;
    if (n>1) {
      density = (100.0 * m) / (n*(n-1));
      //density *= 100;
    }
    else {
      density = 0;
    }
    fprintf(stderr, "n=%d m=%d d=%lf\n", n, m, density);
    if(m < 1500000) { 
      ALPHA = 0.99;
    }
    else if (m>2000000) {
      ALPHA = 0.8;
    }
    else {
      ALPHA = 0.95;
    }
    
    if (m > 2000000) {
      T0 = 0.6;
    }
    else {
      T0 = 0.6;
    }
    
    if(n > 20000) {
      MAX_MV_COEF = 5;
      RESTARTS_LIMIT = 5;
    }
    else if (n < 5000) {
      MAX_MV_COEF = 50;
    }
    else {
      MAX_MV_COEF = 20;
    }
    /*
    if (n>5000) { //sav all if small graphs
      MAX_MV_SAV = 50;
    }
    */
    //MAX_MV_COEF = 20;
  }
  fprintf(stderr, "Args : %f %f %d %d\n", T0, ALPHA, MAX_MV_COEF, RESTARTS_LIMIT);

  //probas(G, probs);

  //Parameters part 2
  //to tune, en fonction de la taille du graphe ? regler la temperature selon ?
  maxMv = MAX_MV_COEF*G->GetNodes();
  //T0 = 0.4;
  
  //à garder ou pas ?!
  //sur 119 1 minute plus efficace, mais dans le temps ?
  //TODO
  if (G->GetNodes()>70000) {  //to check ?
    fprintf(stderr, "Initial topoligical sort greedy...\n");
    //modify S
    initialTopSort(G, S);
  }
  

  //not that because we want to consider only G nodes..
  //std::count(S.begin(), S.end(), -1) 
  fprintf(stderr, "DFVS greedy value = %ld\n", sizeDFVS(G, S));
  /*
  for(auto v : S) {
    printf("%d ", v);
  }
  */

  auto Sstar = recuit(G, S, deltasplus, deltasminus, ok);
  //auto Sstar = recuit(G, S, deltasplus, deltasminus, ok, probs);

/*
  printf("\n\nfinal Sstar\n");
  for(auto a : Sstar) {
    printf("%.0f ", a);
  }
  printf("\n");
*/
  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    if(Sstar[v.GetId()] == -1) {
      printf("%d\n", v.GetId());
    }
  }
  fprintf(stderr, "DFVS final value = %ld + %ld\n", sizeDFVS(G, Sstar),  sol1.size());


  return 0;
}

