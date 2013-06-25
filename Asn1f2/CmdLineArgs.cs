using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace CmdLineArgs
{
    public class CmdArg
    {
        public string Name { get; set; }
        public bool HasValue { get; set; }
        public bool Madatory { get; set; }
    }

    public class CmdLineArguments
    {
        Func<int> _usage;

        public Func<int> usage { get { return _usage ?? (() => -1); } }
        
        /// <summary>
        /// 
        /// </summary>
        /// <param name="ArgName">Long or Short name</param>
        /// <param name="ErrMsg">Error Message to be displayed to user if ArgName is missing</param>
        /// <param name="arg"></param>
        /// <returns></returns>
        /// 

        public  string GetMandatoryArgument(string ArgName, string ErrMsg, params object[] arg) 
        {
            string ret = GetOptionalArgument(ArgName);
            if (ret == null)
            {
                Console.Error.WriteLine(string.Format(ErrMsg, arg));
                Console.Error.WriteLine("Type '{0} -help' to get some help", ExecutableName);
                Environment.Exit(usage());
            }
            return ret;
        }
        
        public string GetMandatoryArgument(string ArgName)
        {
            string LongName = "-" + ArgName;
            return GetMandatoryArgument(ArgName, "Mandatory argument -{0} is missing.", LongName);
        }

        public  string GetOptionalArgument(string ArgName)
        {
            var args = Args;
            string LongName = "-" + ArgName;

            for (int i = 0; i < args.Length; i++)
            {
                if ((args[i] == LongName ) && i < args.Length - 1)
                    return args[i + 1];
            }
            return null;
        }

        public  string GetOptionalArgument(string ArgName, string DefaultValue)
        {
            string ret = GetOptionalArgument(ArgName);
            if (ret == null)
                return DefaultValue;
            return ret;
        }

        public  bool HasArgument(string ArgName)
        {
            string LongName = "-" + ArgName;

            return Args.Any(arg => arg == LongName);
        }

        
        public  IEnumerable<string> OrphanArgs
        {
            get
            {
                var args = Args;
                for (int i = 0; i < args.Length; i++)
                {
                    if (args[i].StartsWith("-"))
                    {
                        var name = new string(args[i].ToCharArray().SkipWhile(c => c == '-').ToArray());
                        if (RegisteredArguments.Where(a => a.Name == name).First().HasValue)
                            i++;
                    }
                    else
                        yield return args[i];
                }
            }
        }

        public void CheckArguments()
        {
            foreach (var m in RegisteredArguments.Where(ar => ar.Madatory))
                GetMandatoryArgument(m.Name, "Mandatory argument -{0} is missing", m.Name);
            if (InvalidArgs.Count() > 0)
            {
                foreach (var s in InvalidArgs)
                    Console.WriteLine("Invalid Argument '{0}'", s);
                Environment.Exit(usage());
            }
        }

        public IEnumerable<string> InvalidArgs
        {
            get
            {
                var allArgs = Args.Where(arg => arg.StartsWith("-"));
                foreach (var arg in allArgs)
                {
                    var name = arg.Substring(1);
                    if (!RegisteredArguments.Any(a => a.Name == name))
                        yield return arg;
                }
            }
        }

        protected CmdLineArguments()
        {

        }

        List<CmdArg> RegisteredArguments = new List<CmdArg>();

        static CmdLineArguments _instance;

        public static CmdLineArguments GetInstance(Func<int> usage)
        {
            if (_instance != null)
                return _instance;
            _instance = new CmdLineArguments();
            _instance._usage = usage;
            return _instance;
        }

        public void RegisterArg(IEnumerable<CmdArg> Args)
        {
            Action<Func<CmdArg, string>> CheckDuplicateNames = lamda =>
            {
                foreach (var dup in Args.GroupBy(lamda))
                {
                    if (dup.Count() > 1)
                    {
                        Console.Error.WriteLine("Duplicate key {0}", dup.Key);
                        Environment.Exit(-1);
                    }
                }
            };

            CheckDuplicateNames(x => x.Name);

            RegisteredArguments.AddRange(Args);
            if (RegisteredArguments.Any(r => r.Madatory && !r.HasValue))
                throw new Exception("Bug: you cannot have mandatory arguments that take no value");
        }

        public static string ExecutableName { get { return Environment.CommandLine.Split(' ')[0]; } }


        static string[] _args;
        public static string[] Args { get { return _args ?? Environment.GetCommandLineArgs().Skip(1).ToArray(); } set { _args = value; } }

    }

}
