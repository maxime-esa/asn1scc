using Service.Dto;

namespace Service
{
    public interface IAsn1Service
    {
        string GetVersion();
        Output BuildAst(InputFiles files);
    }
}
