"""Package the three checked-in manuscript editions for submission or release."""
from pathlib import Path
from shutil import copyfile
from zipfile import ZipFile, ZIP_DEFLATED

root = Path(__file__).resolve().parents[1]
paper = root / "paper" / "v2"
out = root / "dist" / "v2"
out.mkdir(parents=True, exist_ok=True)
for lang in ("en", "ru", "zh"):
    rebuilt = root / "build" / "legacy-v2" / f"{lang}.pdf"
    edition = rebuilt if rebuilt.is_file() else root / "archive" / "paper-i" / f"{lang}.pdf"
    copyfile(edition, out / f"rule110-{lang}.pdf")
    with ZipFile(out / f"rule110-{lang}-source.zip", "w", ZIP_DEFLATED) as archive:
        archive.write(paper / f"{lang}.tex", f"{lang}.tex")
        for font in sorted((paper / "fonts").iterdir()):
            if font.name.startswith(("DejaVu", "NOTICE-DejaVu")) or (
                font.name.startswith(("R110", "NOTICE-CJK")) if lang == "zh"
                else font.name.startswith(("Noto", "NOTICE-Noto"))
            ):
                archive.write(font, font.relative_to(paper))
