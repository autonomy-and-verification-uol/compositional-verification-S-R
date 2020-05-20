datatype coord = coord (x:int,y:int)
datatype seqcoord = seqcoord (seq<(int,int)>)

method PlanReasoningAgent(PlanSet:seq<(seq<(int,int)>)>, threshold : int, b: int) returns (plan:seq<(int,int)>, recharge:bool)
requires [] in PlanSet;
ensures b < threshold  ==> (recharge == true) && plan ==[];//part of third guarantee
ensures threshold <= b && |plan|<= b ==> recharge == false;
ensures plan in PlanSet;//first guarantee
ensures threshold>=b && recharge == false && plan != [] && |plan|<= b ==> forall x :: x in PlanSet  ==> |x| >= |plan|;//last guarantee, also the second one
{
  plan := PlanSet[0];
  recharge := false;
 if (b < threshold) {
    recharge := true;
    plan := [];
  }
  else if (threshold>=b){
    var i:= 0; 
    while(i<|PlanSet|)
    invariant 0<=i<=|PlanSet|;
    invariant plan in PlanSet;
    invariant forall x :: 0 <= x < i ==> |PlanSet[x]| >= |plan|;
    {
      if(|PlanSet[i]| < |plan|)
      {
        plan := PlanSet[i];
      }
      i:= i+1;
    }
  }
}

