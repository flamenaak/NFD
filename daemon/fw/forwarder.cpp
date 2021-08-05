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

#include "ns3/random-variable-stream.h"

#include "utils/ndn-ns3-packet-tag.hpp"

#include <boost/random/uniform_int_distribution.hpp>

#include "ns3/Signer.hpp"

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
        m_caAggregation(false)
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
    //ns3::Ptr<ns3::Node> producer1 = ns3::Names::Find<ns3::Node>("Dst1");

    std::string name = ns3::Names::FindName(node);
    if (name.find("Src") != std::string::npos)
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
//          NS_LOG_UNCOND("local content interest for " << interest.getName().getSubName(1, 1) << " on " << name);
          Interest::InterestType type = Interest::CAR;
          const_cast<Interest &>(interest).setInterestType(type);
          uint8_t seed1[32];
          Signer s(seed1, 32);
          ns3::Ptr<ns3::UniformRandomVariable> uniVar = ns3::CreateObject<ns3::UniformRandomVariable>();
          uniVar->SetAttribute("Min", ns3::DoubleValue(0));
          uniVar->SetAttribute("Max", ns3::DoubleValue(0));
          BloomFilterContainer *container = new BloomFilterContainer(uniVar->GetInteger(0, 1024));
          for (size_t i = 1; i < interest.getName().size() - 1; i++) {
            container->insertIntoBf(interest.getName().getSubName(1, i).toUri());
            
          }
          NS_LOG_UNCOND("Interest for : " << interest.getName().getSubName(1, interest.getName().size() - 2).toUri());
          
          P1 signature = s.sign(container);
          const_cast<Interest &>(interest).addBloomFilter(container);
          const_cast<Interest &>(interest).setSignature(new P1_Affine(signature));
          const_cast<Interest &>(interest).addSigner(new SidPkPair(container->getSignerId(), s.getPublicKey()));

          shared_ptr<Name> nameWithSequence = make_shared<Name>("/CAR");
          nameWithSequence->append(interest.getName().getSubName(interest.getName().size() - 1, 1).toUri());
          const_cast<Interest &>(interest).setName(*nameWithSequence);
          // NS_LOG_UNCOND("new name " << interest.getName().toUri());
        }
        else if (interest.getInterestType() == Interest::CA)
        {
        }
        else if (interest.getInterestType() == Interest::CAR)
        {
          return;
        }
      }
    }
    else if (name.find("Dst") != std::string::npos)
    {
      // for local: this should be some content to be advertised
      // not local:
      // for CA: not important for server
      // for CAR: verify, reconstruct BFs, check BF's against fib (later content store), create CA to advertise present requested files
      if (inFace.isLocal())
      {
        // worry about this later
      }
      else
      {
        if (interest.getInterestType() == Interest::CA)
        {
          return;
        }
        else if (interest.getInterestType() == Interest::CAR)
        {
          bool verified = const_cast<Interest &>(interest).verify(const_cast<Interest &>(interest).getSignerList());
          // prepare CA interest for response
          string nextName = interest.getName().getSubName(1, interest.getName().size() - 2).getSuccessor().toUri();
          shared_ptr<Name> caName = make_shared<Name>("/CA");
          caName->append(nextName);
          shared_ptr<Interest> caInterest = make_shared<Interest>();
          
          caInterest->setName(*caName);
          bool sendCA = false;
          //

          // vector<BloomFilterContainer *> bfs;
          // for (size_t i = 0; i < const_cast<Interest &>(interest).getBloomFilters().size(); i++)
          // {
          //   bfs.push_back(const_cast<Interest &>(interest).getBloomFilters()[i]);
          //   vector<BloomFilterContainer *> tempBfs = const_cast<Interest &>(interest).getBloomFilters()[i]->reconstructBfs();
          //   bfs.insert(bfs.end(), tempBfs.begin(), tempBfs.end());
          // }

          vector<BloomFilterContainer *> bfs = const_cast<Interest &>(interest).getAllBloomFilters();
          vector<BloomFilterContainer *> toBeAdvertised;
          int counter = 0;
          bloom_filter emptyFilter(BF_N, BF_P, BF_SEED);
          // reduce the filters to unique and unionize when possible
          // NS_LOG_UNCOND("bfs size " << bfs.size());
          for (size_t i = 0; i < bfs.size(); i++)
          {
            BloomFilterContainer *current = bfs[i];
            for (size_t j = i; j < bfs.size(); j++)
            {
              if (i == j)
                continue;
              // break the loop if union would exceed inserted element count
              if (current->getBloomFilter()->inserted_element_count_ + bfs[j]->getBloomFilter()->inserted_element_count_ > BF_N)
                break;
              // continue loop if the union is not useful
              if ((*(current->getBloomFilter()) | *(bfs[j]->getBloomFilter())) == *(current->getBloomFilter()))
              { // union does not add anything new
                i++;
                continue;
              }
              if ((*(current->getBloomFilter()) & *(bfs[j]->getBloomFilter())) == *(current->getBloomFilter()))
              { // current is a subset of bfs[j]
                swap(current, bfs[j]);
                i++;
                continue;
              }
              // do union
              current->getBloomFilter()->operator|=(*(bfs[j]->getBloomFilter()));
              current->getBloomFilter()->inserted_element_count_ += bfs[j]->getBloomFilter()->inserted_element_count_;
              i++;
            }
            toBeAdvertised.push_back(current);
          }
          // NS_LOG_UNCOND("tobe advertised size " << toBeAdvertised.size());
          // go through FIB/content store and try to find a match to any of the toBeAdvertised filters
          for (Fib::const_iterator it=m_fib.begin(); it != m_fib.end(); it++) 
          {
            // bloom_filter hashedName(BF_N, BF_P, BF_SEED);
            // for (size_t i = 1; i < it->getPrefix().size(); i++) {
            //   hashedName.insert(it->getPrefix().getSubName(0, i).toUri());
            // }

            // if (hashedName == emptyFilter) continue;

            for (size_t i = 0; i < toBeAdvertised.size(); i++) 
            {
              //BloomFilterContainer c(1, hashedName);
              bool bfContainsName = true;
              for (size_t j = 1; j < it->getPrefix().size(); j++) {
                if (!toBeAdvertised[i]->bfContains(it->getPrefix().getSubName(0, j).toUri())) {
                  bfContainsName = false;
                }
              }
              if (bfContainsName) {
                NS_LOG_UNCOND("FOUND A FILTER IN FIB for name: " << it->getPrefix().toUri());
                caInterest->mergeBf(toBeAdvertised[i]);
                sendCA = true;
              }

              // if ((hashedName & *(toBeAdvertised[i]->getBloomFilter())) == hashedName) {
              //   NS_LOG_UNCOND("FOUND A FILTER IN FIB for name: " << it->getPrefix().toUri());
              //   caInterest->mergeBf(toBeAdvertised[i]);
              //   sendCA = true;
              // } else {
                
              // }
            }
          }
        }
      }
    }
    else if (name.find("Rtr") != std::string::npos)
    {
      // no local interests allowed
      // for CA: verify, put it in the caVec to aggregate, schedule aggregation if it is a first element in the vector
      // for CAR: verify, put it in the carVec to aggregate, schedule aggregation if it is a first element in the vector
      bool verified = const_cast<Interest &>(interest).verify(const_cast<Interest &>(interest).getSignerList());

      if (interest.getInterestType() == Interest::CAR)
      {
        
      } else if (interest.getInterestType() == Interest::CA)
      {

      }
    }

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

  void Forwarder::aggregateInterests(vector<Interest> interests)
  {
    Interest *interest = &interests[0];
    for (size_t i =1; i < interests.size(); i++)
    {
      interest->merge(&interests[i], interests[i].getSignerList());
    }
    
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
    // receive Data
    NFD_LOG_DEBUG("onIncomingData face=" << inFace.getId() << " data=" << data.getName());
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
