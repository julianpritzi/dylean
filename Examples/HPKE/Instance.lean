module

public import Examples.HPKE.Specification
public import Examples.HPKE.Proof

namespace DY.Example.HPKE

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  Hash,
  AKEM,
  AEAD,

instance: HasExecBytes where

#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Random,
  ProtocolEvent HPKEAuthEvent,
  LongTermKeys "HPKE Auth PKI",

instance: HasExecTrace where

#combine +toplevel into
  ProofEntryT,
from
  Network,
  Random,
  ProtocolEvent HPKEAuthEvent,
  LongTermKeys "HPKE Auth PKI",

instance: HasProofTrace where

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  Hash,
  AKEM,
  AEAD,

instance: HasBytesInvariants where

#combine +toplevel into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Random,
  ProtocolEvent HPKEAuthEvent,
  LongTermKeys "HPKE Auth PKI",

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  Hash,
  AKEM,
  AEAD,

instance: HasTraceInvariant where

end

end DY.Example.HPKE
