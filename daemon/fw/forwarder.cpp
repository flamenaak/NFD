/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/**
 * Copyright (c) 2014-2015,  Regents of the University of California,
 *                           Arizona Board of Regents,
 *                           Colorado State University,
 *                           University Pierre & Marie Curie, Sorbonne University,
 *                           Washington University in St. Louis,
 *                           Beijing Institute of Technology,
 *                           The University of Memphis.
 *
 * This file is part of NFD (Named Data Networking Forwarding Daemon).
 * See AUTHORS.md for complete list of NFD authors and contributors.
 *
 * NFD is free software: you can redistribute it and/or modify it under the terms
 * of the GNU General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * NFD is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * NFD, e.g., in COPYING.md file.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "forwarder.hpp"
#include "core/logger.hpp"
#include "core/random.hpp"
#include "strategy.hpp"
#include "face/null-face.hpp"

#include "ns3/node.h"
#include "ns3/node-list.h"
#include "ns3/names.h"
#include "ns3/double.h"
#include "ns3/nstime.h"
#include "ns3/simulator.h"

#include "ns3/random-variable-stream.h"

#include "utils/ndn-ns3-packet-tag.hpp"

#include <boost/random/uniform_int_distribution.hpp>

#include "ns3/Signer.hpp"
#include "ns3/BlsApp.hpp"

using namespace bls_signatures;

namespace nfd
{

  NFD_LOG_INIT("Forwarder");

  using fw::Strategy;

  const Name Forwarder::LOCALHOST_NAME("ndn:/localhost");

  Forwarder::Forwarder()
      : m_faceTable(*this),
        m_fib(m_nameTree),
        m_pit(m_nameTree),
        m_measurements(m_nameTree),
        m_strategyChoice(m_nameTree, fw::makeDefaultStrategy(*this)),
        m_csFace(make_shared<NullFace>(FaceUri("contentstore://"))),
        m_blsAppIndex(1),
        m_carAggregation(false),
        m_caAggregation(false),
        m_caProtected(false),
        m_carProtected(false)
  {
    fw::installStrategies(*this);
    getFaceTable().addReserved(m_csFace, FACEID_CONTENT_STORE);
  }

  Forwarder::~Forwarder()
  {
  }

  void
  Forwarder::onIncomingInterest(Face &inFace, const Interest &interest)
  {
    ns3::Ptr<ns3::Node> node = ns3::NodeList::GetNode(ns3::Simulator::GetContext());
    ns3::Ptr<ns3::BlsApp> app = node->GetApplication(0)->GetObject<ns3::BlsApp>();
    std::string name = ns3::Names::FindName(node);
    bool isRouter1 = name.find("Rtr1") != std::string::npos;

    shared_ptr<fib::Entry> fibEntry = m_fib.findExactMatch(interest.getName());

    if (interest.getInterestType() == Interest::CA || interest.getInterestType() == Interest::CAR) 
    {
      bool verified = const_cast<Interest &>(interest).verify3(app->getSigners()->getAllPairs());
      if (!verified)
      {
        NS_LOG_UNCOND("Could not verify a message: " << interest.getName().toUri());
        const_cast<Interest &>(interest).logDebugContent();
        string typeString = const_cast<Interest&>(interest).getTypeString();
        size_t bfCount = const_cast<Interest&>(interest).getBloomFilters().size();
        size_t reductionCount = 0;
        for (size_t i = 0; i < bfCount; i++) {
          reductionCount += const_cast<Interest&>(interest).getBloomFilters()[i]->getReductions().size();
        }
        // log the unverified message
        ofstream roundtripFile;
        roundtripFile.open("/home/vlado/"+ folderName +"/unverified-" + name + ".csv", ios::out | ios::app);
        roundtripFile << interest.getName().toUri() << "," << typeString << "," << interest.wireEncode().size() << "," << bfCount << "," << reductionCount << "\n";
        roundtripFile.close();
        return;
      }
      // logging for experiments
      if ((interest.getInterestType() == Interest::CA && app->getNodeType() == BlsNodeType::CLIENT)
      || (interest.getInterestType() == Interest::CAR && app->getNodeType() == BlsNodeType::SERVER)
      || app->getNodeType() == BlsNodeType::ROUTER){
        string typeString = const_cast<Interest&>(interest).getTypeString();
        size_t bfCount = const_cast<Interest&>(interest).getBloomFilters().size();
        size_t reductionCount = 0;
        size_t overhead = 96;
        for (size_t i = 0; i < bfCount; i++) {
          reductionCount += const_cast<Interest&>(interest).getBloomFilters()[i]->getReductions().size();
          overhead += const_cast<Interest&>(interest).getBloomFilters()[i]->getByteSize();
        }

        ofstream roundtripFile;
        size_t totalSize = interest.wireEncode().size();
        roundtripFile.open("/home/vlado/"+ folderName +"/interests-" + name + ".csv", ios::out | ios::app);
        roundtripFile << interest.getName().toUri() << "," << typeString << "," << totalSize << "," << overhead << "," << bfCount << "," << reductionCount << "," << totalSize/(bfCount + reductionCount) << "\n";
        roundtripFile.close();
      }
    }
    
    if (app->getNodeType() == BlsNodeType::CLIENT)
    {
      // check if interest came from local face and does not carry BF
      // if local: create a BF from the name, rename the interest with \CAR prefix, insert into pit, send it
      // if not local:
      // for CA:
      // pending: insert to fib and remove from pit
      // not pending: ignore
      // for CAR: discard, not handled by client
      if (inFace.isLocal())
      {
        if (interest.getInterestType() == Interest::content)
        {
          if (fibEntry == NULL)
          {
            app->getTimeMap()->insert(make_pair(interest.getName().toUri(), ns3::Simulator::Now().GetMilliSeconds()));
            shared_ptr<pit::Entry> pitEntry = m_pit.insert(interest).first;
            shared_ptr<Interest> carInterest = make_shared<Interest>(interest);
            carInterest->setInterestType(Interest::CAR);
            Signer* s = app->getSigner();
            
            // create a BF container and populate it with the content name
            BloomFilterContainer *container = new BloomFilterContainer(app->getId());
            size_t o = 0;
            for (size_t i = 1; i < interest.getName().size(); i++) // -1 is to remove the sequence number
            {
              container->insertIntoBf(interest.getName().getSubName(0, i).toUri());
              o = i;
            }
            NS_LOG_UNCOND("Interest for : " << interest.getName().toUri());
            // sign the BF container
            P1 signature = s->sign(container);
            carInterest->addBloomFilter(container);
            carInterest->setSignature(new P1_Affine(signature));
            // carInterest->addSigner(new SidPkPair(app->getId(), s->getPublicKey()));

            // name the CAR, preserving the number at the end
            shared_ptr<Name> nameWithSequence = make_shared<Name>("/CAR");
            nameWithSequence->append(name);
            nameWithSequence->append(interest.getName().getSubName(interest.getName().size() - 1, 1).toUri());
            carInterest->setName(*nameWithSequence);
            // forward CAR to faces
            for (auto it = getFaceTable().begin(); it != getFaceTable().end(); it++) {
              if (it->get()->getId() != inFace.getId() && !it->get()->isLocal()) {
                it->get()->sendInterest(*carInterest);
              }
            }
            return;
          }
          else {
            NS_LOG_UNCOND("THIS INTEREST IS ALREADY IN THE FIB" << interest.getName().toUri());
            fibEntry.get()->getNextHops().begin()->getFace()->sendInterest(interest);
          }
        }
        else if (interest.getInterestType() == Interest::CA)
        {
          return;
        }
        else if (interest.getInterestType() == Interest::CAR)
        {
          return;
        }
      } // inFace.isLocal()
      else {
        if (interest.getInterestType() == Interest::CA)
        {
          vector<BloomFilterContainer*> advertisedBfs = const_cast<Interest &>(interest).getAllBloomFilters();
          NS_LOG_UNCOND("CLIENT received CA with " << advertisedBfs.size() << " BFs");
          // check if the advertised BFs target any of the content names in the PIT
          for (size_t i =0; i < advertisedBfs.size(); i++)
          {
            const pit::Entry *advertisedName = NULL;
            int pitCount = 0;
            for (auto it = m_pit.begin(); it != m_pit.end(); it++)
            {
              pitCount++;
              bool bfContainsName = true;
              // check if all permutations of entry name are contained in BF
              for (size_t j = 1; j < it->getName().size() -1 && bfContainsName; j++) // -1 to avoid the sequence number
              {
                if (!advertisedBfs[i]->bfContains(it->getName().getSubName(0, j).toUri()))
                {
                  bfContainsName = false;
                }
              }
              if (bfContainsName)
              {
                advertisedName = &(*it);
              }
            }
            if (advertisedName != NULL){
              inFace.sendInterest(advertisedName->getInterest());
            }
          }
          return;
        } // interest.getInterestType() == Interest::CA
        else if (interest.getInterestType() == Interest::CAR)
        {
          return;
        }
        else if (interest.getInterestType() == Interest::content)
        {
          return;
        }
      }
    } //CLIENT NODE
    else if (app->getNodeType() == BlsNodeType::SERVER)
    {
      if (!inFace.isLocal())
      {
        if (interest.getInterestType() == Interest::CA)
        {
          return;
        }
        else if (interest.getInterestType() == Interest::CAR)
        {
          // prepare CA interest for response
          string nextName = interest.getName().getSubName(interest.getName().size() - 1, 1).getSuccessor().toUri();
          shared_ptr<Name> caName = make_shared<Name>("/CA");
          caName->append(name);
          caName->append(nextName);
          shared_ptr<Interest> caInterest = make_shared<Interest>();

          caInterest->setName(*caName);
          caInterest->setInterestType(Interest::CA);
          bool sendCA = false;

          // extract BFs from interest
          vector<BloomFilterContainer *> bfs = const_cast<Interest &>(interest).getAllBloomFilters();
          int counter = 0;
          bloom_filter emptyFilter(BF_N, BF_P, BF_SEED);
           NS_LOG_UNCOND("SERVER received CAR with " << bfs.size() << " BFs");
          // go through FIB/content repository and try to find a match to any of the bfs
          vector<Name> advertisedNames;
          for (Fib::const_iterator it = m_fib.begin(); it != m_fib.end(); it++)
          {
            if (it->getPrefix().size() == 0)
              continue;
            for (size_t i = 0; i < bfs.size(); i++)
            {
              bool bfContainsName = true;
              // check if all permutations of entry name are contained in BF
              for (size_t j = 1; j <= it->getPrefix().size() && bfContainsName; j++)
              {
                if (!bfs[i]->bfContains(it->getPrefix().getSubName(0, j).toUri()))
                {
                  bfContainsName = false;
                }
              }
              if (bfContainsName)
              {
                NS_LOG_UNCOND(name << " advertising: " << it->getPrefix().toUri() << "\n for interest " << interest.getName().toUri());
                advertisedNames.push_back(it->getPrefix());
                sendCA = true;
                continue;
              }
            }
          }
          if (sendCA){
            Signer *s = app->getSigner();
            P1 signature;
            // create a BF for all advertised names
            for (size_t i=0; i < advertisedNames.size(); i++)
            {
              BloomFilterContainer *container = new BloomFilterContainer(app->getId());
              for (size_t j = 1; j <= advertisedNames[i].size(); j++)
              {
                container->insertIntoBf(advertisedNames[i].getSubName(0, j).toUri());
              }
              signature.aggregate(s->sign(container));
              caInterest->mergeBf(container);
            }
            // caInterest->addSigner(new SidPkPair(app->getId(), s->getPublicKey()));
            caInterest->setSignature(new P1_Affine(signature));
            inFace.sendInterest(*caInterest);
            //TODO: should probably implement destructor of Interest that deletes all the pointers
          }
          return;
        } 
        else if (interest.getInterestType() == Interest::content)
        {
          // receive routed content interest, try to match it against content that is present
          shared_ptr<fib::Entry> fibEntry = m_fib.findExactMatch(interest.getName().getSubName(0, interest.getName().size() - 1));
          if (static_cast<bool>(fibEntry)) {
            shared_ptr<Data> data = make_shared<Data>();
            data->setName(interest.getName());
            // copied from the producer
            data->setFreshnessPeriod(::ndn::time::milliseconds(0));
            data->setContent(make_shared< ::ndn::Buffer>(8));
            ndn::Signature signature;
            ndn::SignatureInfo signatureInfo(static_cast< ::ndn::tlv::SignatureTypeValue>(255));
            signature.setInfo(signatureInfo);
            signature.setValue(::ndn::nonNegativeIntegerBlock(::ndn::tlv::SignatureValue, app->getId()));
            data->setSignature(signature);
            data->wireEncode();

            NS_LOG_UNCOND(name << " Sending data " << data->getName().toUri() << " for face " << inFace.getId());

            inFace.sendData(*data);
            ++m_counters.getNOutDatas();
          } else {
            // NS_LOG_UNCOND("no FIB entry for " << interest.getName().getSubName(0, interest.getName().size() - 1));
          }
          return;
        }
      } else if (interest.getInterestType() != Interest::default_)
      {
        return;
      }
    } // SERVER node
    else if (app->getNodeType() == BlsNodeType::ROUTER)
    {
      if(inFace.isLocal() && interest.getInterestType() != Interest::default_)
      {
        return;
      }
      if (interest.getInterestType() == Interest::CAR)
      {
        shared_ptr<Interest> interestPtr = make_shared<Interest>(interest);
        vector<BloomFilterContainer*> interestBfs = interestPtr->getAllBloomFilters();
        vector<bloom_filter*> aggregatedBfs;
        
        if(interestBfs.size() == 0) return;

        // store CAR's BFs to be able to handle CAs
        bloom_filter *aggregated = NULL;
        for(size_t i= 0; i < interestBfs.size(); i++)
        {
          if (aggregated == NULL)
          {
            aggregated = new bloom_filter(*interestBfs[i]->getBloomFilter());
          }
          if (aggregated->inserted_element_count_ + interestBfs[i]->getBloomFilter()->inserted_element_count_ > aggregated->predicted_element_count_) {
            // if the BF overflows, make a new one
            aggregatedBfs.push_back(aggregated);
            aggregated = new bloom_filter(*interestBfs[0]->getBloomFilter());
          } else {
            // otherwise union to reduce space requirements
            *aggregated&=*interestBfs[0]->getBloomFilter();
            aggregated->inserted_element_count_ += interestBfs[0]->getBloomFilter()->inserted_element_count_;
          }
          // if its the last one, 
          if (i+1 == interestBfs.size()){
            aggregatedBfs.push_back(aggregated);
          }
        }
        for(size_t i= 0; i < aggregatedBfs.size(); i++)
        {
          m_carStore.insertFilterPair(aggregatedBfs[i], inFace.getId());  
        }
        // aggregate
        while(m_carProtected){
          // wait until aggregation is done
        }
        m_carProtected = true;
        // schedule the forwarding of the CAR for all other faces
        for (auto it = getFaceTable().begin(); it != getFaceTable().end(); it++) {
          if (it->get()->getId()!= inFace.getId() && !it->get()->isLocal()) {
            m_carBuffer.push_back(std::pair<int, Interest>(it->get()->getId(), *interestPtr));
          }
        }
        m_carProtected = false;
        if (!m_carAggregation) {
          ns3::Simulator::Schedule(ns3::MilliSeconds(AGG_TIMER), &Forwarder::aggregateCAR, this);
          m_carAggregation = true;
        }
        return;
      }
      else if (interest.getInterestType() == Interest::CA)
      {
        // extract all BFs
        vector<BloomFilterContainer*> interestBfs = const_cast<Interest &>(interest).getAllBloomFilters();
        list<int> outFaces;
        for(size_t i= 0; i < interestBfs.size(); i++)
        {
          // find any face that was interested in advertised content
          vector<int> tempFaces = m_carStore.matchFilterToFaces(interestBfs[i]->getBloomFilter());
          if (tempFaces.size() > 0)
          {
            // setup the routing via CA
            m_caStore.insertFilterPair(new bloom_filter(*interestBfs[i]->getBloomFilter()), inFace.getId());
          }
          outFaces.insert(outFaces.end(), tempFaces.begin(), tempFaces.end());
        }
        outFaces.sort();
        outFaces.unique();
        while (m_caProtected){} // wait until aggregation is done
        m_caProtected = true;
        // prepare CA for forwarding to all appropriate faces
        for (auto it = outFaces.begin(); it != outFaces.end(); ++it)
        {
          m_caBuffer.push_back(std::pair<int, Interest>(*it, const_cast<Interest &>(interest)));
        }
        // schedule aggregation
        if (!m_caAggregation) {
          ns3::Simulator::Schedule(ns3::MilliSeconds(AGG_TIMER), &Forwarder::aggregateCA, this);
          m_caAggregation = true;
        }
        m_caProtected = false;
        return;
      }
      else if (interest.getInterestType() == Interest::content)
      {
        // check whether there has been a CA for such content
        bloom_filter match(BF_N, BF_P, BF_SEED);
        for (size_t i = 1; i < interest.getName().size() - 1 ; i++) // -1 is to remove the sequence number
        {
          match.insert(interest.getName().getSubName(0, i).toUri());
        }
        // find faces to which to forward
        vector<int> outFaces = m_caStore.matchFilterToFaces(&match);
        if (outFaces.size() == 0) {
          NS_LOG_UNCOND("found no faces for interest " << interest.getName().toUri() << "\n trying to match name " << interest.getName().getSubName(0, interest.getName().size() - 1).toUri());
          return;
        }
        shared_ptr<pit::Entry> pitEntry = m_pit.insert(interest).first;
        const_cast<Interest &>(pitEntry.get()->getInterest()).setIncomingFaceId(inFace.getId());
        // forward "content" interest to all faces that advertised for it
        for (size_t i =0; i < outFaces.size(); i++ )
        {
          m_faceTable.get(outFaces[i])->sendInterest(interest);
        }
        return;
      }
    } // ROUTER

    // receive Interest
    NFD_LOG_DEBUG("onIncomingInterest face=" << inFace.getId() << " interest=" << interest.getName());
    const_cast<Interest &>(interest).setIncomingFaceId(inFace.getId());
    ++m_counters.getNInInterests();

    // /localhost scope control
    bool isViolatingLocalhost = !inFace.isLocal() &&
                                LOCALHOST_NAME.isPrefixOf(interest.getName());
    if (isViolatingLocalhost)
    {
      NFD_LOG_DEBUG("onIncomingInterest face=" << inFace.getId() << " interest=" << interest.getName() << " violates /localhost");
      // (drop)
      return;
    }

    // PIT insert
    shared_ptr<pit::Entry> pitEntry = m_pit.insert(interest).first;

    // detect duplicate Nonce
    int dnw = pitEntry->findNonce(interest.getNonce(), inFace);
    bool hasDuplicateNonce = (dnw != pit::DUPLICATE_NONCE_NONE) ||
                             m_deadNonceList.has(interest.getName(), interest.getNonce());
    if (hasDuplicateNonce)
    {
      // goto Interest loop pipeline
      this->onInterestLoop(inFace, interest, pitEntry);
      return;
    }

    // cancel unsatisfy & straggler timer
    this->cancelUnsatisfyAndStragglerTimer(pitEntry);

    // is pending?
    const pit::InRecordCollection &inRecords = pitEntry->getInRecords();
    bool isPending = inRecords.begin() != inRecords.end();
    if (!isPending)
    {
      if (m_csFromNdnSim == nullptr)
      {
        m_cs.find(interest,
                  bind(&Forwarder::onContentStoreHit, this, ref(inFace), pitEntry, _1, _2),
                  bind(&Forwarder::onContentStoreMiss, this, ref(inFace), pitEntry, _1));
      }
      else
      {
        shared_ptr<Data> match = m_csFromNdnSim->Lookup(interest.shared_from_this());
        if (match != nullptr)
        {
          this->onContentStoreHit(inFace, pitEntry, interest, *match);
        }
        else
        {
          this->onContentStoreMiss(inFace, pitEntry, interest);
        }
      }
    }
    else
    {
      this->onContentStoreMiss(inFace, pitEntry, interest);
    }
  }

    void Forwarder::aggregateCA()
  {
    ns3::Ptr<ns3::Node> node = ns3::NodeList::GetNode(ns3::Simulator::GetContext());
    ns3::Ptr<ns3::BlsApp> app = node->GetApplication(0)->GetObject<ns3::BlsApp>();
    std::string name = ns3::Names::FindName(node);
    //NS_LOG_UNCOND("Time at the aggregation" << ns3::Simulator::Now().GetSeconds());
    while(m_caProtected){}
    m_caProtected = true;
    for (auto it = getFaceTable().begin(); it != getFaceTable().end(); it++) 
    {
      if (it->get()->isLocal()) {
        continue;
      }

      vector<shared_ptr<Interest>> toBeSent;
      shared_ptr<Interest> interest = NULL;
      for (size_t i = 0; i < m_caBuffer.size(); i++)
      {
        if (it->get()->getId() == m_caBuffer[i].first) {
          if (interest == NULL) {
            interest = make_shared<Interest>(m_caBuffer[i].second);  
          } else {
            if (interest->getName().getSubName(0,2) != "/CA/aggregated")
            {
              shared_ptr<Name> newName = make_shared<Name>("/CA/aggregated");
              newName->append(interest->getName().getSubName(1, ndn::Name::npos));
              interest->setName(*newName);
            } 
            else {
              // interest->setName(interest->getName().getSuccessor());
            }
            if (interest->estimateByteSize(false) + m_caBuffer[i].second.estimateByteSize(false) > 3000) { // keep the interest size under Mtu limit
              toBeSent.push_back(interest);
              interest = NULL;
            } else {
              //NS_LOG_UNCOND("Merging interest " << interest->getName() << " with " << m_caBuffer[i].second.getName());
              interest->merge(&(m_caBuffer[i].second));
            }
          }
        }
      }
      if (interest != NULL) {
          toBeSent.push_back(interest);
      }
      // NS_LOG_UNCOND(name << " about to forward interests " << toBeSent.size());

      for (size_t i = 0; i < toBeSent.size(); i++) {
        it->get()->sendInterest(*toBeSent[i]);
        // NS_LOG_UNCOND(name << " Forwardign interest " << toBeSent[i]->getName().toUri());
      }
    }

    m_caBuffer.clear();
    m_caAggregation = false;
    m_caProtected = false;
  }

    void Forwarder::aggregateCAR()
  {
    ns3::Ptr<ns3::Node> node = ns3::NodeList::GetNode(ns3::Simulator::GetContext());
    ns3::Ptr<ns3::BlsApp> app = node->GetApplication(0)->GetObject<ns3::BlsApp>();
    std::string name = ns3::Names::FindName(node);
    bool isRouter1 = name.find("Rtr1") != std::string::npos;

    while(m_carProtected){}
    m_carProtected = true;
    // if(isRouter1)
    // NS_LOG_UNCOND(name << " Time at the aggregation" << ns3::Simulator::Now().GetMilliSeconds() << " buffer size " << m_carBuffer.size());
    for (auto it = getFaceTable().begin(); it != getFaceTable().end(); it++) 
    {
      if (it->get()->isLocal()) {
        continue;
      }

      vector<shared_ptr<Interest>> toBeSent;
      shared_ptr<Interest> interest = NULL;
      for (size_t i = 0; i < m_carBuffer.size(); i++)
      {
        if (it->get()->getId() == m_carBuffer[i].first) {
          if (interest == NULL) {
            interest = make_shared<Interest>(m_carBuffer[i].second);  
          } else {
            if (interest->getName().getSubName(0,2) != "/CAR/aggregated")
            {
              shared_ptr<Name> newName = make_shared<Name>("/CAR/aggregated");
              newName->append(interest->getName().getSubName(1, ndn::Name::npos));
              interest->setName(*newName);
            }
            if (interest->estimateByteSize(false) + m_carBuffer[i].second.estimateByteSize(false) > 3000) { // keep the interest size under Mtu limit (1500)
              // NS_LOG_UNCOND("splitting aggregation");
              toBeSent.push_back(interest);
              interest = NULL;
            } else {
              interest->merge(&(m_carBuffer[i].second));
            }
          }
        }
      }
      if (interest != NULL) {
        toBeSent.push_back(interest);
      }
      // NS_LOG_UNCOND(name << " about to forward interests " << toBeSent.size());

      for (size_t i = 0; i < toBeSent.size(); i++) {
        it->get()->sendInterest(*toBeSent[i]);
        // NS_LOG_UNCOND(name << " Forwardign interest " << toBeSent[i]->getName().toUri() << " to face " << it->get()->getId());
      }
    }
    m_carBuffer.clear();
    m_carAggregation = false;
    m_carProtected = false;
  }

  void
  Forwarder::onContentStoreMiss(const Face &inFace,
                                shared_ptr<pit::Entry> pitEntry,
                                const Interest &interest)
  {
    NFD_LOG_DEBUG("onContentStoreMiss interest=" << interest.getName());

    shared_ptr<Face> face = const_pointer_cast<Face>(inFace.shared_from_this());
    // insert InRecord
    pitEntry->insertOrUpdateInRecord(face, interest);

    // set PIT unsatisfy timer
    this->setUnsatisfyTimer(pitEntry);

    // FIB lookup
    shared_ptr<fib::Entry> fibEntry = m_fib.findLongestPrefixMatch(*pitEntry);

    // dispatch to strategy
    this->dispatchToStrategy(pitEntry, bind(&Strategy::afterReceiveInterest, _1,
                                            cref(inFace), cref(interest), fibEntry, pitEntry));
  }

  void
  Forwarder::onContentStoreHit(const Face &inFace,
                               shared_ptr<pit::Entry> pitEntry,
                               const Interest &interest,
                               const Data &data)
  {
    NFD_LOG_DEBUG("onContentStoreHit interest=" << interest.getName());

    beforeSatisfyInterest(*pitEntry, *m_csFace, data);
    this->dispatchToStrategy(pitEntry, bind(&Strategy::beforeSatisfyInterest, _1,
                                            pitEntry, cref(*m_csFace), cref(data)));

    const_pointer_cast<Data>(data.shared_from_this())->setIncomingFaceId(FACEID_CONTENT_STORE);
    // XXX should we lookup PIT for other Interests that also match csMatch?

    // set PIT straggler timer
    this->setStragglerTimer(pitEntry, true, data.getFreshnessPeriod());

    // goto outgoing Data pipeline
    this->onOutgoingData(data, *const_pointer_cast<Face>(inFace.shared_from_this()));
  }

  void
  Forwarder::onInterestLoop(Face &inFace, const Interest &interest,
                            shared_ptr<pit::Entry> pitEntry)
  {
    NFD_LOG_DEBUG("onInterestLoop face=" << inFace.getId() << " interest=" << interest.getName());

    // (drop)
  }

  /** \brief compare two InRecords for picking outgoing Interest
 *  \return true if b is preferred over a
 *
 *  This function should be passed to std::max_element over InRecordCollection.
 *  The outgoing Interest picked is the last incoming Interest
 *  that does not come from outFace.
 *  If all InRecords come from outFace, it's fine to pick that. This happens when
 *  there's only one InRecord that comes from outFace. The legit use is for
 *  vehicular network; otherwise, strategy shouldn't send to the sole inFace.
 */
  static inline bool
  compare_pickInterest(const pit::InRecord &a, const pit::InRecord &b, const Face *outFace)
  {
    bool isOutFaceA = a.getFace().get() == outFace;
    bool isOutFaceB = b.getFace().get() == outFace;

    if (!isOutFaceA && isOutFaceB)
    {
      return false;
    }
    if (isOutFaceA && !isOutFaceB)
    {
      return true;
    }

    return a.getLastRenewed() > b.getLastRenewed();
  }

  void
  Forwarder::onOutgoingInterest(shared_ptr<pit::Entry> pitEntry, Face &outFace,
                                bool wantNewNonce)
  {
    // NS_LOG_UNCOND("on outgoing interest");
    if (outFace.getId() == INVALID_FACEID)
    {
      NFD_LOG_WARN("onOutgoingInterest face=invalid interest=" << pitEntry->getName());
      return;
    }
    NFD_LOG_DEBUG("onOutgoingInterest face=" << outFace.getId() << " interest=" << pitEntry->getName());

    // scope control
    if (pitEntry->violatesScope(outFace))
    {
      NFD_LOG_DEBUG("onOutgoingInterest face=" << outFace.getId() << " interest=" << pitEntry->getName() << " violates scope");
      return;
    }

    // pick Interest
    const pit::InRecordCollection &inRecords = pitEntry->getInRecords();
    pit::InRecordCollection::const_iterator pickedInRecord = std::max_element(
        inRecords.begin(), inRecords.end(), bind(&compare_pickInterest, _1, _2, &outFace));
    BOOST_ASSERT(pickedInRecord != inRecords.end());
    shared_ptr<Interest> interest = const_pointer_cast<Interest>(
        pickedInRecord->getInterest().shared_from_this());

    if (wantNewNonce)
    {
      interest = make_shared<Interest>(*interest);
      static boost::random::uniform_int_distribution<uint32_t> dist;
      interest->setNonce(dist(getGlobalRng()));
    }

    // insert OutRecord
    pitEntry->insertOrUpdateOutRecord(outFace.shared_from_this(), *interest);

    // send Interest
    outFace.sendInterest(*interest);
    ++m_counters.getNOutInterests();
  }

  void
  Forwarder::onInterestReject(shared_ptr<pit::Entry> pitEntry)
  {
    if (pitEntry->hasUnexpiredOutRecords())
    {
      NFD_LOG_ERROR("onInterestReject interest=" << pitEntry->getName() << " cannot reject forwarded Interest");
      return;
    }
    NFD_LOG_DEBUG("onInterestReject interest=" << pitEntry->getName());

    // cancel unsatisfy & straggler timer
    this->cancelUnsatisfyAndStragglerTimer(pitEntry);

    // set PIT straggler timer
    this->setStragglerTimer(pitEntry, false);
  }

  void
  Forwarder::onInterestUnsatisfied(shared_ptr<pit::Entry> pitEntry)
  {
    NFD_LOG_DEBUG("onInterestUnsatisfied interest=" << pitEntry->getName());

    // invoke PIT unsatisfied callback
    beforeExpirePendingInterest(*pitEntry);
    this->dispatchToStrategy(pitEntry, bind(&Strategy::beforeExpirePendingInterest, _1,
                                            pitEntry));

    // goto Interest Finalize pipeline
    this->onInterestFinalize(pitEntry, false);
  }

  void
  Forwarder::onInterestFinalize(shared_ptr<pit::Entry> pitEntry, bool isSatisfied,
                                const time::milliseconds &dataFreshnessPeriod)
  {
    NFD_LOG_DEBUG("onInterestFinalize interest=" << pitEntry->getName() << (isSatisfied ? " satisfied" : " unsatisfied"));

    // Dead Nonce List insert if necessary
    this->insertDeadNonceList(*pitEntry, isSatisfied, dataFreshnessPeriod, 0);

    // PIT delete
    this->cancelUnsatisfyAndStragglerTimer(pitEntry);
    m_pit.erase(pitEntry);
  }

  void
  Forwarder::onIncomingData(Face &inFace, const Data &data)
  {
    if (!inFace.isLocal()){
      ns3::Ptr<ns3::Node> node = ns3::NodeList::GetNode(ns3::Simulator::GetContext());
      ns3::Ptr<ns3::BlsApp> app = node->GetApplication(0)->GetObject<ns3::BlsApp>();
      std::string name = ns3::Names::FindName(node);
      // NS_LOG_UNCOND(name << " got some data onIncomingData face=" << inFace.getId() << " data=" << data.getName());

      if (app->getNodeType() == BlsNodeType::SERVER)
        return;
      if (app->getNodeType() == BlsNodeType::ROUTER)
      {
        pit::DataMatchResult match = m_pit.findAllDataMatches(data);
        if (match.begin() == match.end())
        {
          NS_LOG_UNCOND(name << " unsolicited data " << data.getName().toUri());
          return;
        }
        for (auto it = match.begin(); it != match.end(); it++)
        {
          // NS_LOG_UNCOND(name << " got some solicited data! " << data.getName().toUri());
          auto fibEntry = m_fib.insert(data.getName()).first;
          fibEntry.get()->addNextHop(inFace.shared_from_this(),1);
          int faceId = it->get()->getInterest().getIncomingFaceId();
          getFaceTable().get(faceId)->sendData(data);
          it->get()->deleteInRecords();
        }
        return;
      }
      if (app->getNodeType() == BlsNodeType::CLIENT)
      {
        pit::DataMatchResult match = m_pit.findAllDataMatches(data);
        if (match.begin() == match.end())
        {
          NS_LOG_UNCOND(name << " CLIENT got unsolicited data " << data.getName().toUri());
          return;
        }
        for (auto it = match.begin(); it != match.end(); it++)
        {
          NS_LOG_UNCOND(name << " CLIENT got some solicited data! " << data.getName().toUri() << " for pit entry " << it->get()->getName().toUri());
          int64_t start = app->getTimeMap()->operator[](data.getName().toUri());
          app->getTimeMap()->erase(data.getName().toUri());
          if (start != 0) {
            int64_t total = ns3::Simulator::Now().GetMilliSeconds() - start;
            // NS_LOG_UNCOND("roundtrip time to get the data: " << total);
            ofstream roundtripFile;
            roundtripFile.open("/home/vlado/"+ folderName +"/roundtrips-" + name + ".csv", ios::out | ios::app);
            roundtripFile << data.getName().toUri() << "," << total << "\n";
            roundtripFile.close();
          }

          auto fibEntry = m_fib.insert(it->get()->getName()).first;
          fibEntry.get()->addNextHop(inFace.shared_from_this(),1);
        }
        return;
      }
    }
    // receive Data

      
    const_cast<Data &>(data).setIncomingFaceId(inFace.getId());
    ++m_counters.getNInDatas();

    // /localhost scope control
    bool isViolatingLocalhost = !inFace.isLocal() &&
                                LOCALHOST_NAME.isPrefixOf(data.getName());
    if (isViolatingLocalhost)
    {
      NFD_LOG_DEBUG("onIncomingData face=" << inFace.getId() << " data=" << data.getName() << " violates /localhost");
      // (drop)
      return;
    }

    // PIT match
    pit::DataMatchResult pitMatches = m_pit.findAllDataMatches(data);
    if (pitMatches.begin() == pitMatches.end())
    {
      // goto Data unsolicited pipeline
      this->onDataUnsolicited(inFace, data);
      return;
    }

    // Remove Ptr<Packet> from the Data before inserting into cache, serving two purposes
    // - reduce amount of memory used by cached entries
    // - remove all tags that (e.g., hop count tag) that could have been associated with Ptr<Packet>
    //
    // Copying of Data is relatively cheap operation, as it copies (mostly) a collection of Blocks
    // pointing to the same underlying memory buffer.
    shared_ptr<Data> dataCopyWithoutPacket = make_shared<Data>(data);
    dataCopyWithoutPacket->removeTag<ns3::ndn::Ns3PacketTag>();

    // CS insert
    if (m_csFromNdnSim == nullptr)
      m_cs.insert(*dataCopyWithoutPacket);
    else
      m_csFromNdnSim->Add(dataCopyWithoutPacket);

    std::set<shared_ptr<Face>> pendingDownstreams;
    // foreach PitEntry
    for (const shared_ptr<pit::Entry> &pitEntry : pitMatches)
    {
      NFD_LOG_DEBUG("onIncomingData matching=" << pitEntry->getName());

      // cancel unsatisfy & straggler timer
      this->cancelUnsatisfyAndStragglerTimer(pitEntry);

      // remember pending downstreams
      const pit::InRecordCollection &inRecords = pitEntry->getInRecords();
      for (pit::InRecordCollection::const_iterator it = inRecords.begin();
           it != inRecords.end(); ++it)
      {
        if (it->getExpiry() > time::steady_clock::now())
        {
          pendingDownstreams.insert(it->getFace());
        }
      }

      // invoke PIT satisfy callback
      beforeSatisfyInterest(*pitEntry, inFace, data);
      this->dispatchToStrategy(pitEntry, bind(&Strategy::beforeSatisfyInterest, _1,
                                              pitEntry, cref(inFace), cref(data)));

      // Dead Nonce List insert if necessary (for OutRecord of inFace)
      this->insertDeadNonceList(*pitEntry, true, data.getFreshnessPeriod(), &inFace);

      // mark PIT satisfied
      pitEntry->deleteInRecords();
      pitEntry->deleteOutRecord(inFace);

      // set PIT straggler timer
      this->setStragglerTimer(pitEntry, true, data.getFreshnessPeriod());
    }

    // foreach pending downstream
    for (std::set<shared_ptr<Face>>::iterator it = pendingDownstreams.begin();
         it != pendingDownstreams.end(); ++it)
    {
      shared_ptr<Face> pendingDownstream = *it;
      if (pendingDownstream.get() == &inFace)
      {
        continue;
      }
      // goto outgoing Data pipeline
      this->onOutgoingData(data, *pendingDownstream);
    }
  }

  void
  Forwarder::onDataUnsolicited(Face &inFace, const Data &data)
  {
    // accept to cache?
    bool acceptToCache = inFace.isLocal();
    if (acceptToCache)
    {
      // CS insert
      if (m_csFromNdnSim == nullptr)
        m_cs.insert(data, true);
      else
        m_csFromNdnSim->Add(data.shared_from_this());
    }

    NFD_LOG_DEBUG("onDataUnsolicited face=" << inFace.getId() << " data=" << data.getName() << (acceptToCache ? " cached" : " not cached"));
  }

  void
  Forwarder::onOutgoingData(const Data &data, Face &outFace)
  {
    NS_LOG_UNCOND("ON OUTGOING DATA");
    if (outFace.getId() == INVALID_FACEID)
    {
      NFD_LOG_WARN("onOutgoingData face=invalid data=" << data.getName());
      return;
    }
    NFD_LOG_DEBUG("onOutgoingData face=" << outFace.getId() << " data=" << data.getName());

    // /localhost scope control
    bool isViolatingLocalhost = !outFace.isLocal() &&
                                LOCALHOST_NAME.isPrefixOf(data.getName());
    if (isViolatingLocalhost)
    {
      NFD_LOG_DEBUG("onOutgoingData face=" << outFace.getId() << " data=" << data.getName() << " violates /localhost");
      // (drop)
      return;
    }

    // TODO traffic manager

    // send Data
    outFace.sendData(data);
    ++m_counters.getNOutDatas();
  }

  static inline bool
  compare_InRecord_expiry(const pit::InRecord &a, const pit::InRecord &b)
  {
    return a.getExpiry() < b.getExpiry();
  }

  void
  Forwarder::setUnsatisfyTimer(shared_ptr<pit::Entry> pitEntry)
  {
    const pit::InRecordCollection &inRecords = pitEntry->getInRecords();
    pit::InRecordCollection::const_iterator lastExpiring =
        std::max_element(inRecords.begin(), inRecords.end(),
                         &compare_InRecord_expiry);

    time::steady_clock::TimePoint lastExpiry = lastExpiring->getExpiry();
    time::nanoseconds lastExpiryFromNow = lastExpiry - time::steady_clock::now();
    if (lastExpiryFromNow <= time::seconds(0))
    {
      // TODO all InRecords are already expired; will this happen?
    }

    scheduler::cancel(pitEntry->m_unsatisfyTimer);
    pitEntry->m_unsatisfyTimer = scheduler::schedule(lastExpiryFromNow,
                                                     bind(&Forwarder::onInterestUnsatisfied, this, pitEntry));
  }

  void
  Forwarder::setStragglerTimer(shared_ptr<pit::Entry> pitEntry, bool isSatisfied,
                               const time::milliseconds &dataFreshnessPeriod)
  {
    time::nanoseconds stragglerTime = time::milliseconds(100);

    scheduler::cancel(pitEntry->m_stragglerTimer);
    pitEntry->m_stragglerTimer = scheduler::schedule(stragglerTime,
                                                     bind(&Forwarder::onInterestFinalize, this, pitEntry, isSatisfied, dataFreshnessPeriod));
  }

  void
  Forwarder::cancelUnsatisfyAndStragglerTimer(shared_ptr<pit::Entry> pitEntry)
  {
    scheduler::cancel(pitEntry->m_unsatisfyTimer);
    scheduler::cancel(pitEntry->m_stragglerTimer);
  }

  static inline void
  insertNonceToDnl(DeadNonceList &dnl, const pit::Entry &pitEntry,
                   const pit::OutRecord &outRecord)
  {
    dnl.add(pitEntry.getName(), outRecord.getLastNonce());
  }

  void
  Forwarder::insertDeadNonceList(pit::Entry &pitEntry, bool isSatisfied,
                                 const time::milliseconds &dataFreshnessPeriod,
                                 Face *upstream)
  {
    // need Dead Nonce List insert?
    bool needDnl = false;
    if (isSatisfied)
    {
      bool hasFreshnessPeriod = dataFreshnessPeriod >= time::milliseconds::zero();
      // Data never becomes stale if it doesn't have FreshnessPeriod field
      needDnl = static_cast<bool>(pitEntry.getInterest().getMustBeFresh()) &&
                (hasFreshnessPeriod && dataFreshnessPeriod < m_deadNonceList.getLifetime());
    }
    else
    {
      needDnl = true;
    }

    if (!needDnl)
    {
      return;
    }

    // Dead Nonce List insert
    if (upstream == 0)
    {
      // insert all outgoing Nonces
      const pit::OutRecordCollection &outRecords = pitEntry.getOutRecords();
      std::for_each(outRecords.begin(), outRecords.end(),
                    bind(&insertNonceToDnl, ref(m_deadNonceList), cref(pitEntry), _1));
    }
    else
    {
      // insert outgoing Nonce of a specific face
      pit::OutRecordCollection::const_iterator outRecord = pitEntry.getOutRecord(*upstream);
      if (outRecord != pitEntry.getOutRecords().end())
      {
        m_deadNonceList.add(pitEntry.getName(), outRecord->getLastNonce());
      }
    }
  }

} // namespace nfd
