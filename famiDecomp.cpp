/*
Copyright (c) of 2018 by Fan Zhang <fanzhang.cs@gmail.com>
*/

#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<vector>
#include<time.h>
#include<iostream>
#include<algorithm>
#include<cstdlib>
#include<ctime>
#include <fstream>
#include "khash.h"

#define testProg 1//0:automation, 1:manual test
#define algorithmChoice 2//0:given k and s, 1:with (k,k-1)-core decomp index, 2: (k,k-1)-core decomp (k-fami), 3: compute k-core, 4: core decomp, 5: compute k-truss
#define computeScore 1//compute active user rate, modularity and cc
#define assesss 0//1:open
#define outputYelp 0
#define outputDBLP 0

using namespace std;

long anchorID;
long maxFollowerNum = -1;
double totalFollowerNum = 0;
long bestAnchorEdgeSize = 0;
char fedges[200], fidnames[150], fstati[200], fmaxCommunityNames[150], fmaxCommunityEdges[150];
long inputK, inputS, datasetID, inikcoreSize, inidegreekNeiSize, visitNumber = 0;
long iniKtrussSize, iniKtrussEdgeSize, iniKm1TrussSize, iniKm1TrussEdgeSize, iniKm2CoreEdgeSize, kcoreVerSize, kcoreEdgeSize, anchoredKtrussSize, anchoredKtrussEdgeSize, ksCoreSize, anchoredKm1TrussEdgeSize;
long triedAncKtrussEdgeSize;
long maxLayerNum, ancInKtNum = 0;
double followerNumber = 0, compTrussTime = 0, constructTimeTag = 0, preprocessingTime = 0, layerBylayerTime = 0, khashConstructTime = 0, edgesBetwNeighTime = 0, edgeBetwNeighRecoTime = 0, layerSearchNeiTime = 0, layerSearchCandTime = 0;
double kCoreTimeTag, kCoreTime = 0, edgeSupportTimeTag, edgeSupportTime = 0, ksCoreTimeTag, km1TrussOnCoreTime = 0, ksCoreTime = 0, kTrussTimeTag, kTrussTime = 0, findBestTimeTag, findBestTime = 0;
double algStartTimeTag, oneKm1TrussTime = 0, oneKtrussOnKm1Time = 0, indexTime = 0, triaCountTime = 0, constructTime = 0;
long triangleNum = 0, triedVerNum = 0, lesskIniNum = 0;
long iniK, insK;
long kmax;

vector<long> degreekVertices, degreekNeighbors, degreekNeiTag, kcoreDeletedTag, degreekVerticesNew, followerTag;//set P and T
vector<long> verSetTag, verOrigIDs, kcoreVerSetIDs, verTag, kcoreTag, verDegree, lesskSet, followersRecord;
vector<long> collapserIDs, numFollowersRecord, anchorIDs;
vector<long> neighborInTriangleIndex;
vector<vector<char> > verNames;
vector<vector<long> > verSet0, verSet, kcoreSet, kcoreSetNeiIndex, kcoreSetSupport, km2coreSetOneCount, km2coreEdgeIDSet, km2coreEdgeNeiSet, verNameIDs, trussEdgeToVerID;
vector<vector<long> > km1ShellVerLayers, km1ShellEdges, km1TrussSupport, km1TrussToDelete, candidateSetLayerNum, candidateSetSearchTag;
vector<long> edgeLayerNumForToDelete;
vector<vector<vector<long> > > km1ShellEdgeLayers, candidateTriaSet, candidateTriaSet1, candidatePatTriaSet, candidatePatTriaSet1, candidateHorTriaSet, candidateHorTriaSet1, candidateSupTriaSet, candidateSupTriaSet1;
vector<long> candNeiCompIndex, kcoreDegree, km1TrussVerices, km1ShellVertices, kTrussVerices, candidateDegree, candidateTrussDegree;
vector<vector<long> > anchoredEdgeSet, candidateEdgeAnchorTag, candidateEdgeTag, candidateEdgeTrussTag, candidateSet, candidateTrussSet, candidateTrussEdgeTag, candidateSetNeiIndex, candidateSetSupport, candidateTrussSetSupport, km1TrussNeiEdgeSet, candidateToDelete, candidateTrussToDelete;
vector<long> km1ShellTriaNeighrbors, km1ShellTriaNeigIndex, km1TrussDegree, candidateVer, candidateTag, toDeleteEdgeSetVid, candidateTrussTag, km2coreOrigTag;
vector<long> degSmallVer, degreeVerDegree;
vector<long> degreeVertices, bestFollowers;
vector<vector<long> > kcoreEdgeTag;
vector<long> coreDecomTag, supBlockTag;
vector<vector<long> > supIncOrder, supOrderIndex;
vector<long> kkcoreDecompTag;
vector<long> degreeIncOrder, blockTag, orderIndex;
vector<long> kkdegreeIncOrder, kkblockTag, kkorderIndex;

vector<long> coreTag, coreDegree, coreVertices, coreIndex;
vector<vector<long> > inikcoreSupport, coreSet, coreEdgeSupport, coreEdgeTag, coreNeiIndex;
vector<vector<long> > toDeleteEdgeSet;

KHASH_MAP_INIT_INT(32, long)
vector<khash_t(32)*> kcoreTable, coreTable;

string infile, outfile;

void dataInput()
{
	double time0 = (double)clock() / CLOCKS_PER_SEC;

	//read edges, build verSet //need first row ordered data
	long vertexID, neighborID;
	vector<long> verSetInsertion;
	ifstream fin;
	fin.open(infile.c_str());

	if (!fin)
	{
		cout << "Open Fail";
		exit(1);
	}
	else
	{
		long verid = -1, vid, nid;
		char fech = 's';
		while (!fin.eof())
		{
			fin >> vertexID >> neighborID;
			vid = verSetTag[vertexID];
			nid = verSetTag[neighborID];
			if (vid < 0)
			{
				verid++;
				verSetTag[vertexID] = verid; //vertexID -> vid
				verOrigIDs.push_back(vertexID); //vid -> vertexID
				vid = verid;
			}
			if (nid < 0)
			{
				verid++;
				verSetTag[neighborID] = verid;
				verOrigIDs.push_back(neighborID);
				nid = verid;
			}
			if (verSet0.size() == 0)
			{
				verSetInsertion.clear();
				verSetInsertion.push_back(vid);
				verSetInsertion.push_back(nid);
				verSet0.push_back(verSetInsertion);
			}
			else
			{
				if (vid == verSet0[verSet0.size() - 1][0])
				{
					verSet0[verSet0.size() - 1].push_back(nid);
				}
				else
				{
					verSetInsertion.clear();
					verSetInsertion.push_back(vid);
					verSetInsertion.push_back(nid);
					verSet0.push_back(verSetInsertion);
				}
			}
		}
	}
	fin.close();

	//1. remove duplicates£¬ create verSet; 2. make unpaired edge to be paired ; 3. remove self loop
	vector<vector<long> > verNei;
	verNei.resize(verOrigIDs.size());
	for (long i = 0; i < verSet0.size(); i++)
	{
		long id = verSet0[i][0];
		for (long j = 1; j < verSet0[i].size(); j++)
		{
			long nid = verSet0[i][j];
			verNei[id].push_back(nid);
			verNei[nid].push_back(id); //duplicate
		}
	}
	long eNum = 0;
	vector<long> vTag, nTag;
	vTag.resize(verOrigIDs.size());
	nTag.resize(verOrigIDs.size(), -1);
	verSet.resize(verOrigIDs.size());
	long nT = 0;
	for (long i = 0; i < verNei.size(); i++)
	{
		for (long j = 0; j < verNei[i].size(); j++)
		{
			long nid = verNei[i][j];
			if (nTag[nid] != nT && nid != i) //remove duplicate neighbor and self loop
			{
				verSet[i].push_back(nid);
				nTag[nid] = nT;
				eNum++;
			}
		}
		nT++;
	}
	vector<long>().swap(vTag);
	vector<long>().swap(nTag);
	vector<vector<long> >().swap(verNei);

	cout << "Vertices: " << verSet.size() << " Edges: " << eNum / 2 << " Avg. Degree: " << double(eNum) / 2 / verSet.size() << "\n";
	double time1 = (double)clock() / CLOCKS_PER_SEC;
	cout << "Read time: " << time1 - time0 << "\n";
}

bool compareDegree(const long &a, const long &b)//sort comparison for degree increasing
{
	return verSet[a].size() < verSet[b].size();
}

bool compareSupport(const vector<long> &a, const vector<long> &b)//sort comparison for support increasing
{
	return kcoreSetSupport[a[0]][a[1]] < kcoreSetSupport[b[0]][b[1]];
}

void computeEdgeSupport()
{
	int ret, is_missing;
	khash_t(32) *h;
	khiter_t kr;
	vector<long> setInsertion, setInsertion0, setInsertion1, edgeInsertion;

	kcoreSetSupport.clear();
	kcoreSetNeiIndex.clear();
	kcoreTable.clear();
	kcoreEdgeTag.clear();
	double khashStart, khashEnd;

	for (long i = 0; i < verSet.size(); i++)
	{
		setInsertion.clear();
		setInsertion1.clear();
		setInsertion0.clear();

		h = kh_init(32);
		for (long j = 0; j < verSet[i].size(); j++)
		{
			long nid = verSet[i][j];
			setInsertion.push_back(-1);
			setInsertion1.push_back(1);
			setInsertion0.push_back(0);
			khashStart = (double)clock() / CLOCKS_PER_SEC;
			kr = kh_put(32, h, nid, &ret);
			kh_val(h, kr) = j;
			khashEnd = (double)clock() / CLOCKS_PER_SEC;
			khashConstructTime += khashEnd - khashStart;

			if (i < nid)
			{
				edgeInsertion.clear();
				edgeInsertion.push_back(i);
				edgeInsertion.push_back(j);
				supIncOrder.push_back(edgeInsertion);
			}

		}
		kcoreEdgeTag.push_back(setInsertion1);
		kcoreSetSupport.push_back(setInsertion);
		kcoreSetNeiIndex.push_back(setInsertion);
		kcoreTable.push_back(h);
		supOrderIndex.push_back(setInsertion0);
	}

	//compute edge support
	lesskSet.clear();
	kcoreDegree.clear();
	long matchIdInIndexVer, indexIdInMatchVer;
	for (long i = 0; i < verSet.size(); i++)
	{
		for (long j = 0; j < verSet[i].size(); j++)
		{
			if (kcoreSetSupport[i][j] < 0)
			{
				long nid = verSet[i][j];
				long indexId, matchId;
				long support = 0;
				if (verSet[i].size() < verSet[nid].size())
				{
					indexId = i;
					matchId = nid;
				}
				else
				{
					indexId = nid;
					matchId = i;
				}
				//find common neighbors
				h = kcoreTable[matchId];
				kr = kh_get(32, h, indexId);
				indexIdInMatchVer = kh_val(h, kr);
				for (long k = 0; k < verSet[indexId].size(); k++)
				{
					long knid = verSet[indexId][k];
					kr = kh_get(32, h, knid);
					if (kr != kh_end(h))
					{
						support++;
					}
				}
				h = kcoreTable[indexId];
				kr = kh_get(32, h, matchId);
				matchIdInIndexVer = kh_val(h, kr);

				kcoreSetSupport[indexId][matchIdInIndexVer] = support;
				kcoreSetSupport[matchId][indexIdInMatchVer] = support;
				kcoreSetNeiIndex[indexId][matchIdInIndexVer] = indexIdInMatchVer;
				kcoreSetNeiIndex[matchId][indexIdInMatchVer] = matchIdInIndexVer;
			}
		}
		kcoreDegree.push_back(verSet[i].size());
	}
}

void updateSDegree(long curK)
{
	long id, iid, nid, oid, onid, deg, bid1, temp;

	for (long i = supBlockTag[curK - 1]; i < supBlockTag[curK]; i++)
	{
		id = supIncOrder[i][0];
		iid = supIncOrder[i][1];
		if (kcoreEdgeTag[id][iid])
		{
			nid = verSet[id][iid];
			//do id
			if (kkcoreDecompTag[id] > curK)
			{
				oid = kkorderIndex[id];
				deg = kkcoreDecompTag[id];
				bid1 = kkblockTag[deg];
				temp = kkdegreeIncOrder[bid1];
				kkdegreeIncOrder[bid1] = id;
				kkdegreeIncOrder[oid] = temp;
				kkcoreDecompTag[id]--;
				kkblockTag[deg]++;
				kkorderIndex[id] = bid1;
				kkorderIndex[temp] = oid;
			}

			//do nid
			if (kkcoreDecompTag[nid] > curK)
			{
				onid = kkorderIndex[nid];
				deg = kkcoreDecompTag[nid];
				bid1 = kkblockTag[deg];
				temp = kkdegreeIncOrder[bid1];
				kkdegreeIncOrder[bid1] = nid;
				kkdegreeIncOrder[onid] = temp;
				kkcoreDecompTag[nid]--;
				kkblockTag[deg]++;
				kkorderIndex[nid] = bid1;
				kkorderIndex[temp] = onid;
			}

		}
	}
}


void updateSDegree1(long i, long curK)
{
	long id, iid, nid, oid, onid, deg, bid1, temp;

	//for (long i = bid0; i < bid; i++)
	{
		id = supIncOrder[i][0];
		iid = supIncOrder[i][1];
		//if (kcoreEdgeTag[id][iid])
		{
			nid = verSet[id][iid];
			//do id
			if (kkcoreDecompTag[id] > curK - 1)
			{
				oid = kkorderIndex[id];
				deg = kkcoreDecompTag[id];
				bid1 = kkblockTag[deg];
				temp = kkdegreeIncOrder[bid1];
				kkdegreeIncOrder[bid1] = id;
				kkdegreeIncOrder[oid] = temp;
				kkcoreDecompTag[id]--;
				kkblockTag[deg]++;
				kkorderIndex[id] = bid1;
				kkorderIndex[temp] = oid;
			}

			//do nid
			if (kkcoreDecompTag[nid] > curK - 1)
			{
				onid = kkorderIndex[nid];
				deg = kkcoreDecompTag[nid];
				bid1 = kkblockTag[deg];
				temp = kkdegreeIncOrder[bid1];
				kkdegreeIncOrder[bid1] = nid;
				kkdegreeIncOrder[onid] = temp;
				kkcoreDecompTag[nid]--;
				kkblockTag[deg]++;
				kkorderIndex[nid] = bid1;
				kkorderIndex[temp] = onid;
			}
		}
	}
}

void updateSupport(long id0, long j, long curK)
{
	khash_t(32) *h;
	khiter_t kr;
	long id, iid, oid, onid, sup, bid1, temp, tempi, bid;
	long indexId, matchId, vidInMatchVer;
	long nid = verSet[id0][j];
	//find common neighbors
	if (verSet[id0].size() < verSet[nid].size())
	{
		indexId = id0;
		matchId = nid;
	}
	else
	{
		indexId = nid;
		matchId = id0;
	}
	h = kcoreTable[matchId];
	for (long k = 0; k < verSet[indexId].size(); k++)
	{
		long knid = verSet[indexId][k];
		if (kkcoreDecompTag[knid] > curK - 1)
		{
			kr = kh_get(32, h, knid);
			vidInMatchVer = kh_value(h, kr);
			if (kr != kh_end(h))
			{
				if (kcoreEdgeTag[indexId][k] && kcoreEdgeTag[matchId][vidInMatchVer]) //correctness! knid-indexid and knid-matchid exist
				{
					if (id0 == indexId)
					{
						sup = kcoreSetSupport[matchId][vidInMatchVer];
						if (sup > curK - 2)
						{
							//update neighboring edges of matchId-knid
							kcoreSetSupport[matchId][vidInMatchVer]--;
							long vidInKnid = kcoreSetNeiIndex[matchId][vidInMatchVer];
							kcoreSetSupport[knid][vidInKnid]--;
							//update support
							bid = supBlockTag[sup];
							temp = supIncOrder[bid][0];
							tempi = supIncOrder[bid][1];
							if (matchId < knid)
							{
								oid = supOrderIndex[matchId][vidInMatchVer];
								supIncOrder[bid][0] = matchId;
								supIncOrder[bid][1] = vidInMatchVer;
								supIncOrder[oid][0] = temp;
								supIncOrder[oid][1] = tempi;
								supBlockTag[sup]++;
								supOrderIndex[matchId][vidInMatchVer] = bid;
								supOrderIndex[temp][tempi] = oid;
							}
							else
							{
								oid = supOrderIndex[knid][vidInKnid];
								supIncOrder[bid][0] = knid;
								supIncOrder[bid][1] = vidInKnid;
								supIncOrder[oid][0] = temp;
								supIncOrder[oid][1] = tempi;
								supBlockTag[sup]++;
								supOrderIndex[knid][vidInKnid] = bid;
								supOrderIndex[temp][tempi] = oid;
							}
							//update degree
							if (sup == curK - 1)
							{
								updateSDegree1(bid, curK);
							}
						}
					}
					else
					{
						sup = kcoreSetSupport[indexId][k];
						if (sup > curK - 2)
						{
							//update neighboring edges of indexId-knid
							kcoreSetSupport[indexId][k]--;
							long vidInKnid = kcoreSetNeiIndex[indexId][k];
							kcoreSetSupport[knid][vidInKnid]--;

							//update support
							bid = supBlockTag[sup];
							temp = supIncOrder[bid][0];
							tempi = supIncOrder[bid][1];
							if (indexId < knid)
							{
								oid = supOrderIndex[indexId][k];
								supIncOrder[bid][0] = indexId;
								supIncOrder[bid][1] = k;
								supIncOrder[oid][0] = temp;
								supIncOrder[oid][1] = tempi;
								supBlockTag[sup]++;
								supOrderIndex[indexId][k] = bid;
								supOrderIndex[temp][tempi] = oid;
							}
							else
							{
								oid = supOrderIndex[knid][vidInKnid];
								supIncOrder[bid][0] = knid;
								supIncOrder[bid][1] = vidInKnid;
								supIncOrder[oid][0] = temp;
								supIncOrder[oid][1] = tempi;
								supBlockTag[sup]++;
								supOrderIndex[knid][vidInKnid] = bid;
								supOrderIndex[temp][tempi] = oid;
							}
							//update degree
							if (sup == curK - 1)
							{
								updateSDegree1(bid, curK);
							}
						}
					}
				}
			}
		}
	}
}

void algorithm()
{
	long degree;
	for (long i = 0; i < verSet.size(); i++)
	{
		degree = verSet[i].size();
		verDegree.push_back(degree);
		verTag.push_back(1);
	}

	double iterationStartTag = (double)clock() / CLOCKS_PER_SEC;

	computeEdgeSupport();

	edgeSupportTimeTag = (double)clock() / CLOCKS_PER_SEC;
	edgeSupportTime = edgeSupportTimeTag - iterationStartTag;

	sort(supIncOrder.begin(), supIncOrder.end(), compareSupport);
	long bi = 0;
	for (long i = 0; i < supIncOrder.size(); i++)
	{
		long id = supIncOrder[i][0];
		long iid = supIncOrder[i][1];
		long sup = kcoreSetSupport[id][iid];
		supOrderIndex[id][iid] = i; //p
		while (sup >= bi)
		{
			supBlockTag.push_back(i); //b
			bi++;
		}
	}

	kkdegreeIncOrder.clear();
	kkorderIndex.clear();
	kkblockTag.clear();
	kkcoreDecompTag.clear();
	for (long i = 0; i < verSet.size(); i++) //index
	{
		kkdegreeIncOrder.push_back(i); //D
		long deg = verSet[i].size();
		kkcoreDecompTag.push_back(deg); //d
		kkorderIndex.push_back(0);
	}

	sort(kkdegreeIncOrder.begin(), kkdegreeIncOrder.end(), compareDegree);
	bi = 0;
	for (long i = 0; i < kkdegreeIncOrder.size(); i++)
	{
		long id = kkdegreeIncOrder[i];
		long deg = kkcoreDecompTag[id];
		kkorderIndex[id] = i; //p
		while (deg >= bi)
		{
			kkblockTag.push_back(i); //b
			bi++;
		}
	}
	long curK = 1; long sizeG = verSet.size();

	long id0, bid0, bid, bid1, nid, ndeg, oid, inid, temp, sup;

	while (sizeG > 0)
	{
		bid0 = kkblockTag[curK - 1];
		for (long i = bid0; i < kkblockTag[curK]; i++)
		{
			id0 = kkdegreeIncOrder[i];
			kkcoreDecompTag[id0] = curK - 1;
			sizeG--;
			for (long j = 0; j < verSet[id0].size(); j++)
			{
				nid = verSet[id0][j];
				ndeg = kkcoreDecompTag[nid];
				inid = kcoreSetNeiIndex[id0][j];

				if (ndeg > curK - 1 && kcoreEdgeTag[id0][j])
				{
					sup = kcoreSetSupport[id0][j];
					if (sup > curK - 2)
					{
						//update degree
						oid = kkorderIndex[nid];
						bid1 = kkblockTag[ndeg];
						temp = kkdegreeIncOrder[bid1];
						kkdegreeIncOrder[bid1] = nid;
						kkdegreeIncOrder[oid] = temp;
						kkcoreDecompTag[nid]--;
						kkblockTag[ndeg]++;
						kkorderIndex[nid] = bid1;
						kkorderIndex[temp] = oid;

						//update support block id
						if (id0 < nid)
						{
							oid = supOrderIndex[id0][j];
						}
						else
						{
							oid = supOrderIndex[nid][inid];
						}
						bid1 = supBlockTag[sup];
						if (oid == bid1)
						{
							supBlockTag[sup]++;
						}
					}

					//update support
					updateSupport(id0, j, curK);
				}
				kcoreEdgeTag[id0][j] = 0;
				kcoreEdgeTag[nid][inid] = 0;
			}
		}

		updateSDegree(curK);
		curK += 1;

	}
	kmax = kkcoreDecompTag[kkdegreeIncOrder[kkdegreeIncOrder.size() - 1]];
}

void dataOutput(double &runtime)
{
	char *writeTemp;
	char record[100];
	FILE *fs;
	fs = fopen(outfile.c_str(), "a");
	char fsch = 0;

	if (fs == NULL)
	{
		printf("ERROR!");
		exit(1);
	}
	else
	{
		sprintf(record, "%.2lf", runtime);
		fwrite(record, sizeof(*record), strlen(record), fs);
		fsch = putc('\t', fs);

		sprintf(record, "km%ld", kmax);
		fwrite(record, sizeof(*record), strlen(record), fs);
		fsch = putc('\n', fs);
	}
}

int main(int argc, char *argv[])
{
	//configuration
	long maxVerID = 100000000; //max vertex id
	verSetTag.resize(maxVerID, -1);
	infile = "dataset.txt";
	outfile = "result.txt";

	//input data 
	dataInput();

	//algorithm start
	algStartTimeTag = (double)clock() / CLOCKS_PER_SEC;

	//compute ks-core
	algorithm();
	cout << "k_max: " << kmax << "\n";

	double runtime = (double)clock() / CLOCKS_PER_SEC - algStartTimeTag;
	printf("time: %lf\n", runtime);

	//write
	dataOutput(runtime);

	return 0;
}
