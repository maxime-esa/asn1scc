using Service.Dto;

namespace Service
{
    public interface IAsn1Service
    {
        string GetVersion();
        string BuildAst(Files files);
    }
}
