
[{|
  bcontext := [];
  bbody :=
    tApp
      (tConst
          (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
          "routestartfn"%bs) [])
      [tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} 0 []]
|};
{|
  bcontext := [];
  bbody :=
    tApp
      (tConst
          (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
          "routecenterfn"%bs) [])
      [tApp
          (tConstruct
            {|
              inductive_mind :=
                (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} 1 [])
          [tConstruct
            {|
              inductive_mind :=
                (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} 0 []];
        tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} 0 [];
        tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} 1 []]
|};
{|
  bcontext := [];
  bbody :=
    tApp
      (tConst
          (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
          "routecenterfn"%bs) [])
      [tApp
          (tConstruct
            {|
              inductive_mind :=
                (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} 1 [])
          [tApp
            (tConstruct
                {|
                  inductive_mind :=
                    (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                    "nat"%bs);
                  inductive_ind := 0
                |} 1 [])
            [tConstruct
                {|
                  inductive_mind :=
                    (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                    "nat"%bs);
                  inductive_ind := 0
                |} 0 []]];
        tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} 1 [];
        tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} 2 []]
|};
{|
  bcontext := [];
  bbody :=
    tApp
      (tConst
          (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
          "routeendfn"%bs) [])
      [tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} 2 []]
|}])
: term
