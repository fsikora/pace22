//PACE 2022 Heuristic solver for DFVS
//Florian Sikora

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

//SNAP graphs
typedef PNGraph PGraph;  // directed graph
typedef PUNGraph UGraph; // undirected graph
typedef PGraph::TObj::TNodeI TNodeI;

// Default Parameters
double T0 = 0.5;
double ALPHA = 0.9;
int maxMv;
int MAX_MV_COEF = 10;
int RESTARTS_LIMIT = 60;
int MAX_RESTARTS = 100;
int LIMIT_COLD_RESTART = 10;
float lambd = 0.3;
int MAX_MV_SAV = 100;

// optil.io signal handling
volatile sig_atomic_t tle = 0;
void term(int signum)
{
  tle = 1;
}

/********************************************************/
/* READING GRAPH                                        */
/********************************************************/

// from PACE organizers
PGraph readGraph()
{
  std::string line;

  std::getline(std::cin, line);
  // skip comments
  while (line[0] == '%')
  {
    std::getline(std::cin, line);
  }

  int N, M, ew;
  std::stringstream ss(line);
  ss >> N >> M >> ew;
  // Graph graph(N);
  PGraph G = PGraph::TObj::New();

  long source = 1;
  while (std::getline(std::cin, line))
  {

    if (line[0] == '%')
    { // a comment in the file
      continue;
    }
    std::stringstream ss(line);

    G->AddNodeUnchecked(source);
    long target;
    while (ss >> target)
    {
      G->AddNodeUnchecked(target);
      G->AddEdge(source, target);
    }
    if (std::cin.eof())
    {
      break;
    }
    source++;
  }
  IAssert(G->GetNodes() == N);
  IAssert(G->GetEdges() == M);
  return G;
}

/********************************************************/
/* REDUCTION RULES                                      */
/********************************************************/

bool delEdgesBetweenScc(const PGraph &G, std::vector<int> &cclabel)
{
  fprintf(stderr, "Computing Strong CC\n");
  // get Strong Con Comp
  TCnComV SCnComV;
  TSnap::GetSccs(G, SCnComV);
  int found = false;
  // labelling the CC
  for (int ccid = 0; ccid < SCnComV.Len(); ccid++)
  {
    TCnCom cc = SCnComV[ccid];
    for (int i = 0; i < cc.Len(); i++)
    {
      int v = cc[i];
      cclabel[v] = ccid;
    }
  }

  if (SCnComV.Len() > 1)
  {
    fprintf(stderr, "May have some edges to delete\n");
    std::vector<std::pair<int, int>> todelete;
    // look for edges between StrongCC
    for (auto e = G->BegEI(); e < G->EndEI(); e++)
    {
      int u = e.GetSrcNId();
      int v = e.GetDstNId();
      if (cclabel[u] != cclabel[v])
      {
        // delete
        todelete.push_back(std::pair(u, v));
        found = true;
      }
    }
    for (auto e : todelete)
      G->DelEdge(e.first, e.second);
  }
  return found;
}

bool isClique(const UGraph &U, int vid)
{
  auto v = U->GetNI(vid);
  for (int e1 = 0; e1 < v.GetDeg(); e1++)
  {
    for (int e2 = e1 + 1; e2 < v.GetDeg(); e2++)
    {
      if (!U->IsEdge(v.GetNbrNId(e1), v.GetNbrNId(e2)))
        return false;
    }
  }
  return true;
}

bool isPiVertex(const PGraph &G, const UGraph &U, int vid)
{
  auto v = G->GetNI(vid);
  for (int e = 0; e < v.GetDeg(); e++)
  {
    int u = v.GetNbrNId(e);
    if (!U->IsEdge(vid, u))
      return false;
  }
  return true;
}

bool condition1(const PGraph &G, const UGraph &U, int uid, int vid)
{
  auto u = G->GetNI(uid);
  auto v = G->GetNI(vid);

  for (int e = 0; e < u.GetInDeg(); e++)
  {
    auto predU = u.GetInNId(e);

    if (!U->IsEdge(predU, uid))
    { // predU is a non-Pi-Pred
      // must be also a pred of v
      if (!G->IsEdge(predU, vid))
      {
        return false; // some of Pu is not in Pv
      }
    }
  }
  return true;
}

bool condition2(const PGraph &G, const UGraph &U, int uid, int vid)
{
  auto v = G->GetNI(vid);
  for (int e = 0; e < v.GetOutDeg(); e++)
  {
    auto succV = v.GetOutNId(e);
    if (!U->IsEdge(vid, succV))
    { // succV is a non-Pi-Succ
      // must be also a succ of u
      if (!G->IsEdge(uid, succV))
      {
        return false; // some of Sv is not in Su
      }
    }
  }
  return true;
}

bool applyPIEreduction(const PGraph &G, std::vector<int> &cclabel)
{
  // check for PIE edges
  bool reduced = false;
  std::vector<std::pair<int, int>> pie;

  for (auto e = G->BegEI(); e < G->EndEI(); e++)
  {
    int u = e.GetSrcNId();
    int v = e.GetDstNId();
    if (u < v && G->IsEdge(v, u))
    {
      pie.push_back(std::pair(u, v));
      pie.push_back(std::pair(v, u));
    }
  }
  fprintf(stderr, "Tempo deletion of %ld PIE edges\n", pie.size());
  for (auto e : pie)
  {
    G->DelEdge(e.first, e.second);
  }

  reduced = delEdgesBetweenScc(G, cclabel);

  // put back
  for (auto e : pie)
    G->AddEdge(e.first, e.second);

  return reduced;
}

bool applyCOREreduction(const PGraph &G, const UGraph &U, std::vector<int> &sol)
{
  bool reduced = false;

  auto cmp = [&G](int a, int b)
  {
    TNodeI aid = G->GetNI(a);
    TNodeI bid = G->GetNI(b);
    // need a total order for set, need to find a way to tie break
    if (aid.GetDeg() == bid.GetDeg())
      return a < b;
    else
      return (aid.GetDeg() < bid.GetDeg());
  };

  std::vector<int> piv;
  for (auto v = U->BegNI(); v < U->EndNI(); v++)
    piv.push_back(v.GetId());
  // take vertices by increasing degrees
  std::sort(piv.begin(), piv.end(), cmp);

  std::unordered_set<int> invalid;
  std::vector<int> todel;
  for (auto v : piv)
  { // piv in ascending degree
    if (G->IsNode(v) && (invalid.find(v) == invalid.end()))
    { // not present
      // check if v and N(v) forms a clique
      if (isPiVertex(G, U, v) && isClique(U, v))
      {
        fprintf(stderr, "Found a clique on PI-vertex %d\n", v);
        auto vni = U->GetNI(v);
        int iniDeg = vni.GetDeg();
        for (int e = 0; e < iniDeg; e++)
        {
          sol.push_back(vni.GetNbrNId(e));
          todel.push_back(vni.GetNbrNId(e));
        }
        todel.push_back(v);

        for (auto v : todel)
        {
          G->DelNode(v);
          U->DelNode(v);
        }
        todel.clear();
        reduced = true;
      }
      else
      {
        // invalid v and its neigbors
        invalid.insert(v);
        auto vni = U->GetNI(v);
        for (int e = 0; e < vni.GetDeg(); e++)
          invalid.insert(vni.GetNbrNId(e));
      }
    }
  }
  return reduced;
}

bool applyDOMEreduction(const PGraph &G, const UGraph &U)
{
  bool reduced = false;
  std::vector<std::pair<int, int>> todelete;
  for (auto e = G->BegEI(); e < G->EndEI(); e++)
  {
    // check if e is dominated
    int u = e.GetSrcNId();
    int v = e.GetDstNId();
    if (!U->IsEdge(u, v) && (condition1(G, U, u, v) || condition2(G, U, u, v)))
    {
      todelete.push_back(std::pair(u, v));
      reduced = true;
    }
  }
  if (todelete.size() > 0)
    fprintf(stderr, "Found some dominated edges %ld!\n", todelete.size());
  for (auto e : todelete)
    G->DelEdge(e.first, e.second);
  return reduced;
}

/* Main function for reduction rules */
std::vector<int> reduction(const PGraph &G)
{
  std::vector<int> sol;
  bool reduced = true;
  // before the reduction to avoid labels problems!
  std::vector<int> cclabel; // in which cc is each vertex. Reserved before the reduction to index correctly
  cclabel.reserve(G->GetNodes() + 1);

  while (reduced) // reduce until all rules failed
  {
    // basic reductions first (Levy & Low)
    reduced = false;
    std::vector<int> toRemove;
    fprintf(stderr, "n,m:%d %d\n", G->GetNodes(), G->GetEdges());

    for (auto v = G->BegNI(); v < G->EndNI(); v++)
    {
      if (v.GetInDeg() == 0 || v.GetOutDeg() == 0)
      {
        toRemove.push_back(v.GetId());
        reduced = true;
      }
      else if (v.GetInDeg() == 1 && !G->IsEdge(v.GetId(), v.GetId()))
      {
        auto u = v.GetInNId(0); // only one
        for (int e = 0; e < v.GetOutDeg(); e++)
        {
          G->AddEdge(u, v.GetOutNId(e));
        }
        toRemove.push_back(v.GetId());
        reduced = true;
      }
      else if (v.GetOutDeg() == 1 && !G->IsEdge(v.GetId(), v.GetId()))
      {
        auto u = v.GetOutNId(0); // only one
        for (int e = 0; e < v.GetInDeg(); e++)
        {
          G->AddEdge(v.GetInNId(e), u);
        }
        toRemove.push_back(v.GetId());
        reduced = true;
      }
      // forced in solution
      else if (G->IsEdge(v.GetId(), v.GetId()))
      {
        toRemove.push_back(v.GetId());
        sol.push_back(v.GetId());
        reduced = true;
      }
    }
    for (auto v : toRemove)
    {
      G->DelNode(v);
    }
    
    //3 next rules are from Lin & Jou
    // PIE
    if (!reduced)
    { // at the last moment, check if there are edges between SCC we can delete
      reduced = applyPIEreduction(G, cclabel);

      if (!reduced)
      { // CORE
        UGraph U = UGraph::TObj::New();

        for (auto e = G->BegEI(); e < G->EndEI(); e++)
        {
          int u = e.GetSrcNId();
          int v = e.GetDstNId();
          if (u < v && G->IsEdge(v, u))
          {
            U->AddNodeUnchecked(u);
            U->AddNodeUnchecked(v);
            U->AddEdge(u, v);
          }
        }

        reduced = applyCOREreduction(G, U, sol);

        if (!reduced)
        { // DOME
          reduced = applyDOMEreduction(G, U);
        }
      }
    }
  }
  return sol;
}


/********************************************************/
/* GREEDY INITIAL SOLUTION                              */
/********************************************************/

bool canBeAddInTopol(const PGraph &G, const std::vector<double> &S, TNodeI v)
{
  for (int e = 0; e < v.GetOutDeg(); e++)
  {
    if (S[v.GetOutNId(e)] != -1)
      return false;
  }
  return true;
}

void initialTopSort(const PGraph &G, std::vector<double> &S)
{
  std::vector<TNodeI> nodes;
  nodes.reserve(G->GetNodes());
  for (auto v = G->BegNI(); v < G->EndNI(); v++)
  {
    nodes.push_back(v);
  }
  // must be ascending
  std::sort(nodes.begin(), nodes.end(), [](TNodeI a, TNodeI b)
            { return (a.GetInDeg() - a.GetOutDeg()) < (b.GetInDeg() - b.GetOutDeg()); });

  int label = 1;
  for (auto v : nodes)
  {
    if (canBeAddInTopol(G, S, v))
    {
      S[v.GetId()] = label;
      label++;
    }
  }
}



/***********************************************************/
/* LOCAL SEARCH SIMULATED ANNEALING (Galinier et al. 2013) */
/***********************************************************/

long int sizeDFVS(const PGraph &G, const std::vector<double> &S)
{
  long int size = 0;
  for (auto v = G->BegNI(); v < G->EndNI(); v++)
  {
    if (S[v.GetId()] == -1)
      size++;
  }
  return size;
}

int popRandom(std::vector<int> &vector)
{
  // get a random element
  // swap with the last
  // remove last
  int idx = rand() % vector.size();
  auto elt = vector[idx];
  std::swap(vector[idx], vector.back());
  vector.pop_back();
  return elt;
}

//unused
int popSampled(std::vector<int> &candidates, const std::vector<double> &probas)
{
  double sum = 0;
  for (int i = 1; i < candidates.size(); i++)
  {
    auto v = candidates[i];
    sum += probas[v];
  }
  double stop = (rand() / (RAND_MAX + 1.0)) * sum;
  sum = 0;
  for (int i = 1; i < candidates.size(); i++)
  {
    auto elt = candidates[i];
    sum += probas[elt];
    if (sum >= stop)
    {
      std::swap(candidates[i], candidates.back());
      candidates.pop_back();
      return elt;
    }
  }
  IAssert(1 != 1); // shouldn't be here
  return 0;
}

int iplus(const PGraph &G, const std::vector<double> &S, int v)
{
  auto node = G->GetNI(v);
  int min = G->GetNodes() + 1;
  for (int e = 0; e < node.GetOutDeg(); e++)
  {
    int idtop = S[node.GetOutNId(e)];
    if (idtop != -1 && idtop < min)
    {
      min = idtop;
    }
  }
  return min;
}

int iminus(const PGraph &G, const std::vector<double> &S, int v)
{
  int max = 0;
  auto node = G->GetNI(v);

  for (int e = 0; e < node.GetInDeg(); e++)
  {
    int idtop = S[node.GetInNId(e)];
    if (idtop != -1 && idtop > max)
    {
      max = idtop;
    }
  }
  return max + 1;
}

std::vector<int> CVminus(const PGraph &G, const std::vector<double> &S, int v, int i)
{
  std::vector<int> sol;
  auto node = G->GetNI(v);
  for (int e = 0; e < node.GetInDeg(); e++)
  {
    auto j = node.GetInNId(e);
    if (S[j] != -1 && S[j] >= i)
    {
      sol.push_back(j);
    }
  }
  return sol;
}

std::vector<int> CVplus(const PGraph &G, const std::vector<double> &S, int v, int i)
{
  std::vector<int> sol;
  auto node = G->GetNI(v);
  for (int e = 0; e < node.GetOutDeg(); e++)
  {
    auto j = node.GetOutNId(e);
    if (S[j] != -1 && S[j] < i)
    {
      sol.push_back(j);
    }
  }
  return sol;
}

int delta(const PGraph &G, const std::vector<double> &S, int v, int i)
{
  return -1 + CVplus(G, S, v, i).size() + CVminus(G, S, v, i).size();
}

void updateVertex(const PGraph &G, const std::vector<double> &S, int v, std::vector<int> &deltasplus, std::vector<int>&deltasminus, std::vector<bool> &ok)
{
  deltasplus[v] = delta(G, S, v, iplus(G, S, v));
  deltasminus[v] = delta(G, S, v, iminus(G, S, v));
  ok[v] = true;
}

void relabel(const PGraph &G, std::vector<double> &S)
{
  std::map<double, int> selectedS;

  for (auto v = G->BegNI(); v < G->EndNI(); v++)
  {
    if (S[v.GetId()] != -1)
    {
      selectedS.insert({S[v.GetId()], v.GetId()});
    }
  }

  int label = 1;
  // map label -> vertex

  // https://stackoverflow.com/questions/38164274/c-modifying-key-for-all-map-elements
  std::map<double, int> modifiedS;
  for (auto it = selectedS.begin(); it != selectedS.end();)
  {
    S[it->second] = label;
    auto nh = selectedS.extract(it++);
    nh.key() = label;
    label++;
    modifiedS.insert(modifiedS.end(), std::move(nh)); // should be O(1) given the hint
  }
  modifiedS.swap(selectedS);
}

void applymove(const PGraph &G, std::vector<double> &S, int v, int b, std::vector<int> &candidates, std::vector<bool> &ok)
{
  S[v] = b - 0.001;
  // v in candidates allready removed
  for (auto i : CVplus(G, S, v, b))
  {
    S[i] = -1;
    candidates.push_back(i);
    ok[i] = false;
    auto iid = G->GetNI(i);
    for (int e = 0; e < iid.GetOutDeg(); e++)
      ok[iid.GetOutNId(e)] = false;
    for (int e = 0; e < iid.GetInDeg(); e++)
      ok[iid.GetInNId(e)] = false;
  }
  for (auto i : CVminus(G, S, v, b))
  {
    S[i] = -1;

    candidates.push_back(i);
    ok[i] = false;
    auto iid = G->GetNI(i);
    for (int e = 0; e < iid.GetOutDeg(); e++)
    {
      ok[iid.GetOutNId(e)] = false;
    }
    for (int e = 0; e < iid.GetInDeg(); e++)
    {
      ok[iid.GetInNId(e)] = false;
    }
  }
  ok[v] = false;
  auto vid = G->GetNI(v);
  for (int e = 0; e < vid.GetOutDeg(); e++)
    ok[vid.GetOutNId(e)] = false;
  for (int e = 0; e < vid.GetInDeg(); e++)
    ok[vid.GetInNId(e)] = false;

  if (S[v] - 0.001 < floor(S[v]))
  {
    fprintf(stderr, "Too much small steps %f for vertex %d, relabel...\n", S[v], v);
    relabel(G, S);
  }
}

float RandomBetween(float smallNumber, float bigNumber)
{
  float diff = bigNumber - smallNumber;
  return (((float)rand() / RAND_MAX) * diff) + smallNumber;
}

/* Main SA function*/
std::vector<double> SA(const PGraph &G, std::vector<double> &S, std::vector<int> &deltasplus, std::vector<int> &deltasminus, std::vector<bool> &ok)
{
  // std::vector<double> SA(const PGraph& G, std::vector<double>& S, int* deltasplus, int* deltasminus, std::vector<bool>& ok, std::vector<double>& probas) {
  double T = T0;
  int nbFails = 0;
  std::vector<double> Sstar(S);
  double Tstar = T0;
  std::vector<int> candidates; // list of candidates to get random
  int SvalInt = 0;             // it is dfvs size !
  int nbRestarts = 0;
  int movesSinceSav = 0;

  candidates.reserve(G->GetNodes()); // certainly too much

  for (auto v = G->BegNI(); v < G->EndNI(); v++)
  {
    if (S[v.GetId()] == -1)
    {
      candidates.push_back(v.GetId());
      SvalInt++;
    }
  }
  int Sstarval = SvalInt;

  while (!tle && nbRestarts < MAX_RESTARTS)
  {
    int nbMv = 0;
    bool fail = true;

    while (nbMv < maxMv && !tle)
    {
      auto v = popRandom(candidates);
      // auto v = popSampled(candidates, probas);
      int b;
      int Delta;
      movesSinceSav++;

      if (!ok[v])
        updateVertex(G, S, v, deltasplus, deltasminus, ok);

      if (rand() % 2 == 0)
      { //+
        b = iplus(G, S, v);
        Delta = deltasplus[v];
      }
      else
      {
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
      if (Delta <= 0 || exp(-Delta / T) >= ((double)rand() / (RAND_MAX)))
      {
        applymove(G, S, v, b, candidates, ok);
        SvalInt += Delta;
        nbMv++;
        // to avoid copy of the best solution, we do it only if we didn't save for a while (or if the solution is small, meaning that we will not recopy a lot anymore)
        if (SvalInt < Sstarval && (SvalInt < 10000 || movesSinceSav >= MAX_MV_SAV))
        { // best so far
          if (SvalInt % 1000 == 0)
            fprintf(stderr, "DFVS size %d\n", SvalInt);
          // save the best
          movesSinceSav = 0;
          Sstar.assign(S.begin(), S.end()); // spend a lot of time here!!
          Sstarval = SvalInt;
          Tstar = T;
          fail = false;
          nbRestarts = 0;
          if (SvalInt == 0)
          {
            fprintf(stderr, "Opti !\n");
            return Sstar;
          }
        }
      }
      else
      {
        // v is now again a candidate, it wasn't choose
        candidates.push_back(v);
      }
    }
    T = T * ALPHA;
    if (fail)
    {
      nbFails++;
      if (nbFails == RESTARTS_LIMIT || T < 0.01)
      {
        fprintf(stderr, "Too much fails or temp %f too small, restart with the previous best %d at temp %f\n", T, Sstarval, Tstar);
        // restart with the current best instead of deeping..
        nbFails = 0;
        nbRestarts++;
        // T = Tstar;
        // T = Tstar + 0.1;
        T = std::min(std::max(0.2, Tstar + RandomBetween(-0.1, 0.6)), 0.9);
        // ALPHA = std::min(std::max(0.5, ALPHA + RandomBetween(-0.2, 0.2)), 0.99);

        MAX_MV_COEF = std::min(std::max(7, MAX_MV_COEF + int(RandomBetween(-10, 10))), 80);
        maxMv = MAX_MV_COEF * G->GetNodes();

        fprintf(stderr, "Temp is now %f with ALPHA %f and MAXMV %d\n", T, ALPHA, MAX_MV_COEF);
        S.clear();

        S.assign(Sstar.begin(), Sstar.end());
        SvalInt = Sstarval;

        // update candidates and selecteed!
        candidates.clear();
        // data is not reliable anymore
        std::fill(ok.begin(), ok.end(), false);

        for (auto v = G->BegNI(); v < G->EndNI(); v++)
        {
          if (S[v.GetId()] == -1)
          {
            candidates.push_back(v.GetId());
          }
        }
      }
    }
    else
    {
      fprintf(stderr, "reloop after %d fails, nbMv %d\n", nbFails, nbMv);
      nbFails = 0;
    }
  }
  fprintf(stderr, "Too much restarts %d (or TLE), best is %d\n", nbRestarts, Sstarval);
  return Sstar;
}

//unused
void probas(const PGraph &G, std::vector<double> &probs)
{
  // maxs
  int dm = 0;
  int dp = 0;
  for (auto v = G->BegNI(); v < G->EndNI(); v++)
  {
    if (v.GetInDeg() > dm)
      dm = v.GetInDeg();
    if (v.GetOutDeg() > dp)
      dp = v.GetOutDeg();
  }

  int m = dm + dp;

  for (auto v = G->BegNI(); v < G->EndNI(); v++)
  {
    probs[v.GetId()] = m - v.GetInDeg() + v.GetOutDeg() - lambd * (std::abs(v.GetInDeg() - v.GetOutDeg()));
  }
}





/********************************************************/
/* MAIN                                                 */
/********************************************************/

int main(int argc, char *argv[])
{
  // optl.io
  struct sigaction action;
  memset(&action, 0, sizeof(struct sigaction));
  action.sa_handler = term;
  sigaction(SIGTERM, &action, NULL);

  std::ios_base::sync_with_stdio(false);

  fprintf(stderr, "Creating graph:\n");
  PGraph G = readGraph();
  fprintf(stderr, "Graph created.\n");
  IAssert(G->IsOk());

  // std::srand(0);
  std::srand(time(NULL));

  /*inits*/
  // arrays of size G+1 (since start at 1)
  //int deltasplus[G->GetNodes() + 1];
  //int deltasminus[G->GetNodes() + 1];
  //can't use array for big graphs
  std::vector<int> deltasplus(G->GetNodes() + 1);
  std::vector<int> deltasminus(G->GetNodes() + 1);

  std::vector<bool> ok(G->GetNodes() + 1, false);
  std::vector<double> S(G->GetNodes() + 1, -1);
  // std::vector<double> probs(G->GetNodes()+1, 0);


  /* RR*/
  fprintf(stderr, "Starting reduction rules...\n");
  std::vector<int> sol1 = reduction(G);
  // removed vertices printing
  fprintf(stderr, "Reduced vertices : %ld\n", sol1.size());
  for (auto v : sol1)
  {
    std::cout << v << std::endl;
  }


  // for SA parameter testing
  if (argc == 5)
  {
    fprintf(stderr, "Arguments setting:\n");
    T0 = atof(argv[1]);
    ALPHA = atof(argv[2]);
    MAX_MV_COEF = atoi(argv[3]);
    RESTARTS_LIMIT = atoi(argv[4]);
  }
  else
  {
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
    if (n > 1)
      density = (100.0 * m) / (n * (n - 1));
    else
      density = 0;
    fprintf(stderr, "n=%d m=%d d=%lf\n", n, m, density);
    if (m < 1500000)
      ALPHA = 0.99;
    else if (m > 2000000)
      ALPHA = 0.8;
    else
      ALPHA = 0.95;

    if (m > 2000000)
      T0 = 0.6;
    else
      T0 = 0.6;

    if (n > 20000)
    {
      MAX_MV_COEF = 5;
      RESTARTS_LIMIT = 5;
    }
    else if (n < 5000)
      MAX_MV_COEF = 50;
    else
      MAX_MV_COEF = 20;
  }
  fprintf(stderr, "Args : %f %f %d %d\n", T0, ALPHA, MAX_MV_COEF, RESTARTS_LIMIT);

  // probas(G, probs);
  //set the number of moves accoding the the graph size after the RR
  maxMv = MAX_MV_COEF * G->GetNodes();

  if (G->GetNodes() > 70000)
  {
    fprintf(stderr, "Initial topoligical sort greedy...\n");
    // modify S
    initialTopSort(G, S);
  }
  // not that because we want to consider only G nodes..
  fprintf(stderr, "DFVS greedy value = %ld\n", sizeDFVS(G, S));

  /*SA local search*/
  auto Sstar = SA(G, S, deltasplus, deltasminus, ok);
  // auto Sstar = SA(G, S, deltasplus, deltasminus, ok, probs);

  // solution printing
  for (auto v = G->BegNI(); v < G->EndNI(); v++)
    if (Sstar[v.GetId()] == -1)
      printf("%d\n", v.GetId());
  fprintf(stderr, "DFVS final value = %ld + %ld\n", sizeDFVS(G, Sstar), sol1.size());

  return 0;
}
