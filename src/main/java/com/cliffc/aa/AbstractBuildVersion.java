package com.cliffc.aa;

import com.cliffc.aa.util.SB;
  
public abstract class AbstractBuildVersion {
  abstract public String branchName();
  abstract public String lastCommitHash();
  abstract public String describe();
  abstract public String projectVersion();
  abstract public String compiledOn();
  abstract public String compiledBy();
  @Override public String toString() {
    SB sb = new SB().p("aa v").p(projectVersion()).p('\n');
    sb.p(compiledBy()).p(" ").p(branchName()).p(" ").p(lastCommitHash()).p(" on ").p(compiledOn());
    return sb.toString();
  }
}
