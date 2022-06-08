#include "stdafx.h"
#include <iostream> 
#include <vector>
#include <sstream> 
#include <algorithm> 
#include <array>
#include <signal.h>
#include <unistd.h>
//#include <unordered_set>
#include <map>

//je suis meilleur sur les petites instances mais battu sur les grosses ?! (en solu)
//loin sur le h_099 (50) ou le h_119 (60) par exemple
//pas une histoire de dense (je suis bon sur la 62 qui est dense). n ?
//regarder comment optimiser les parametres, avec des papiers type celui des coréens qui font du simplexe..
//voir les restarts apres un nombre de fails en reprenant la temperature du moment où la best temps et la best solution so far
//pb, les graphes avec bcp de sommets ne vont pas y arriver ?
//gros pb : sur les gros graphes, je fais moins de moves que le nombre de sommets !!!
//quand doit insérer : decaller "à la main", et quand doit delete, delete "a la main". Garder un tableau des labels vers les sommets pour pas avoir à parcours tout ?
//linkedlist : si j'arrive a lui donner les iterateurs, constant insert et delete? (constant avec l'iterator) -> reste quand meme a mettre à jour le label donc non



//TODO autre stucture que map

typedef PNGraph PGraph;  //   directed graph
typedef PGraph::TObj::TNodeI TNodeI;

//Parameters part 2
double T0 = 0.3;
double alpha = 0.99;
int maxMv;
int maxMvCoef = 20;
int maxFails = 100;

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

std::vector<int> reduction(const PGraph& G) {
  std::vector<int> sol;
  bool reduced = true;

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
    //toRemove.clear();

    //DelEdge
    //DelNode

  }

  return sol;
}

bool canBeAddInTopol(const PGraph& G, std::vector<int> S, TNodeI v) {
  for(int e = 0 ; e<v.GetOutDeg() ; e++) {
    if(S[v.GetOutNId(e)] != -1) return false;
  }
  return true;
}

void initialTopSort(const PGraph& G, std::vector<int>& S) {
  //TODO tenter ignorer le gros degrés du debut pour les gros graphes denses ?
  //pas sur,la 119 est merdique mais pas de gros degrés pour autant
  std::vector<TNodeI> nodes;
  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    nodes.push_back(v);
  }
  
  std::sort(nodes.begin(), nodes.end(), [](TNodeI a, TNodeI b) {
        return (a.GetInDeg()-a.GetOutDeg()) < (b.GetInDeg()-b.GetOutDeg());
    });
  //must be ascending  
  
  /*
  for(auto v : nodes)
    std::cout << v.GetId() << ' ' << v.GetInDeg() << ' ' << v.GetOutDeg() << std::endl;
  */
  int label = 1;
  for(auto v : nodes) {
    if (canBeAddInTopol(G, S, v)) {
      S[v.GetId()] = label;
      label++;
    }
  }
}

long int sizeDFVS(const PGraph& G, const std::vector<int> S) {
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

int iplus(const PGraph& G, std::vector<int> S, int v, int nbLabels) {
  auto node = G->GetNI(v);
//  if(node.GetOutDeg() > 0) {
//    int min = std::numeric_limits<int>::max();
    //int min = SvalInt + 1; //TODO to check
    //int min = G->GetNodes()+1;
    int min = nbLabels+1;
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

int iminus(const PGraph& G, std::vector<int> S, int v) {
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

std::vector<int> CVminus(const PGraph& G, std::vector<int> S, int v, int i) {
  std::vector<int> sol;
  auto node = G->GetNI(v);
  for(int e=0 ; e<node.GetInDeg() ; e++) {
    auto j = node.GetInNId(e);
    if (S[j] != -1 && S[j]>=i) {
      sol.push_back(j);
    }
  }
  return sol;
}

std::vector<int> CVplus(const PGraph& G, std::vector<int> S, int v, int i) {
  std::vector<int> sol;
  auto node = G->GetNI(v);
  for(int e=0 ; e<node.GetOutDeg() ; e++) {
    auto j = node.GetOutNId(e);
    if (S[j] != -1 && S[j]<i) {
      sol.push_back(j);
    }
  }
  return sol;
}

int delta(const PGraph& G, std::vector<int> S, int v, int i) {
  return -1 + CVplus(G, S, v, i).size() + CVminus(G, S, v, i).size();
}

void updateVertex(const PGraph& G, std::vector<int> S, int v, int* deltasplus, int* deltasminus, std::vector<bool>& ok, int nbLabels) {
  deltasplus[v] = delta(G, S, v, iplus(G, S, v, nbLabels));
  deltasminus[v] = delta(G, S, v, iminus(G, S, v));
  ok[v] = true;
}

void relabel(const PGraph& G, std::vector<float>& S,
std::map<float, int>& selectedS) {
  //TODO pas besoin de trier si selectedS est trié ?
  //TODO pas relabel si rien a changé ?!
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
  std::map<float, int> modifiedS;
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

/*
void applymove_map(const PGraph& G, std::vector<float>& S, int v, int b,  std::map<float, int>& selectedS, std::vector<int>& candidates, std::vector<bool>& ok) {
  //printf("apply move on %d, %d \n", v, b);
  S[v] = b-0.1;
  selectedS.insert({S[v], v});
  //v in candidates allready removed
  for(auto i : CVplus(G, S, v, b)) {
    selectedS.erase(S[i]);  //il faut supprimer la clef qui est l'indice dans le topo !
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
    selectedS.erase(S[i]);
    
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
  relabel(G, S, selectedS);
}
*/

void shiftLabels(std::vector<int>& S, std::vector<int>& selectedS, int startIndex, int endIndex, int change) {
  for(int i = startIndex ; i<endIndex ; i++) {
    int v = selectedS[i];
    //printf("Change label of vertex %d supposed to be %d, was %d by %d\n", v, i, S[v], change);
    IAssert(S[v] != -1);
    S[v] += change;  
  }
}

void applymove(const PGraph& G, std::vector<int>& S, int v, int b,  std::vector<int>& selectedS, std::vector<int>& candidates, std::vector<bool>& ok, int& nbLabels) {
  //printf("apply move on %d giving label %d \n", v, b);
  
  //will insert v with label b : needs to shift the rest
  //selectedS.insert(b, v); //move the rest
  //selectedS.insert(selectedS.begin()+b, v);
  //make room

  //printf("d---- %d\n", S[807]);
  /*
  printf("d---- \n");
  for(auto v : S) {
    printf("%d ", v);
  }
  printf("\n");
  for(int a = 0 ; a<nbLabels+1 ; a++) { //TODO aller jusqu'à nbLabels+1 !
    printf("%d ", selectedS[a]);
  }
  printf("f----\n");
  */
  nbLabels++;;
  for(int i = nbLabels ; i>b ; i--) {
    selectedS[i] = selectedS[i-1];
  }
  selectedS[b] = v;
  S[v] = b;
  //printf("Shift vertices from %d to %d by +1\n", b+1, nbLabels);
  shiftLabels(S, selectedS, b+1, nbLabels+1, 1);
  
  //v in candidates allready removed
  for(auto i : CVplus(G, S, v, b)) {
    //selectedS.erase(selectedS.begin()+S[i]);
    //printf("remove label of %d\n", i);
    nbLabels--;
    //decal
    for(int idx = S[i] ; idx < nbLabels+1 ; idx++) {  //we also want to move the nbLabel index
      selectedS[idx] = selectedS[idx+1];
    }
    shiftLabels(S, selectedS, S[i], nbLabels+1, -1);
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
    //printf("remove label of %d\n", i);
    //selectedS.erase(selectedS.begin()+S[i]);
    nbLabels--;
    //decal
    for(int idx = S[i] ; idx < nbLabels+1 ; idx++) {
      selectedS[idx] = selectedS[idx+1];
    }
    shiftLabels(S, selectedS, S[i], nbLabels+1, -1);
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
  //relabel(G, S, selectedS);

/*
printf("After move, should be correct :\n");
  for(auto v : S) {
    printf("%d ", v);
  }
  printf("\nf--\n");
*/
}


std::vector<int> recuit(const PGraph& G, std::vector<int>& S, int* deltasplus, int* deltasminus, std::vector<bool>& ok) {
  double T = T0;
  int nbFails = 0;
  //TODO voir comment eviter les float !
  std::vector<int> Sstar(S);
  //std::unordered_set<int> candidates;
  std::vector<int> candidates;  //list of candidates to get random
  //std::unordered_set<int> selectedS;  //TODO useful?
  //comparer avec un treeset ?
  //std::map<float, int> selectedS;
  std::vector<int>selectedS;
  int SvalInt=0;  //TODO c'est le dfvs size !!!!
  int nbLabels=0;
  selectedS.reserve(G->GetNodes()+1);
  selectedS[0] = 0;

  for (auto v = G->BegNI() ; v<G->EndNI() ; v++) {
    if(S[v.GetId()] == -1){
      candidates.push_back(v.GetId());
      SvalInt++;

    }  
    else {
      //selectedS.insert({S[v.GetId()], v.GetId()}); 
      auto label = S[v.GetId()];
      selectedS[label] = v.GetId();
      nbLabels++;
    }
  }
  int Sstarval = SvalInt;

  //while(nbFails<maxFails && !tle) {
  while(!tle) {
    int nbMv = 0;
    bool fail = true;
    while (nbMv < maxMv && !tle) {
      auto v = popRandom(candidates);
      int b;
      int Delta;

      if (!ok[v]) {
        updateVertex(G, S, v, deltasplus, deltasminus, ok, nbLabels);
      }

      if(rand()%2==0) { //+
        b = iplus(G, S, v, nbLabels);
        Delta = deltasplus[v];
      }
      else {
        b = iminus(G, S, v);
        Delta = deltasminus[v];
      }

      if (Delta <=0 || exp(-Delta/T) >= ((double) rand() / (RAND_MAX))) {
        //applymove(G, S, v, b, selectedS, candidates, ok);
        applymove(G, S, v, b, selectedS, candidates, ok, nbLabels);
        SvalInt += Delta;
        nbMv++;
        if (SvalInt < Sstarval) { //best so far
          fprintf(stderr, "DFVS size %d\n", SvalInt);
          //fprintf(stderr, "real size ?%ld\n", sizeDFVS(G, S));
          //save the best
          Sstar.assign(S.begin(), S.end());
          Sstarval = SvalInt;
          fail = false;
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
    if (fail) {
      nbFails++;
      fprintf(stderr, "Fails %d, current sol is %d\n", nbFails, SvalInt);
    }
    else {
      fprintf(stderr, "reloop %d nbMv %d\n", nbFails, nbMv);
      nbFails = 0;
    }
    T = T*alpha;
  }
  fprintf(stderr, "Too much fails, best is %d\n", Sstarval);
  return Sstar;
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
  std::srand(0);
  float lambd = 0.2;

  //arrays of size G+1 (since start at 1)
  int deltasplus[G->GetNodes()+1];
  int deltasminus[G->GetNodes()+1];

  std::vector<bool> ok(G->GetNodes()+1, false);
  std::vector<int> S(G->GetNodes()+1, -1);

  //std::cout << ok.at(5) << ", " << deltasminus[5]+1 << S.at(10);

  fprintf(stderr, "Starting reduction rules...\n");
  
  std::vector<int> sol1 = reduction(G);
  fprintf(stderr, "Reduced vertices : %ld\n", sol1.size());
  for(auto v : sol1) {
    std::cout << v << std::endl;
  }
  

  //Parameters part 2
  //to tune, en fonction de la taille du graphe ? regler la temperature selon ?
  maxMv = maxMvCoef*G->GetNodes();
  //T0 = 0.4;
  
  //à garder ou pas ?!
  
  if (G->GetNodes()>0) {
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

